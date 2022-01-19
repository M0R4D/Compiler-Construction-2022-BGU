#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

(* ----------------------------------------- BEGINNING OF CONSTS VARS TABLE IMPLEMENTATION ----------------------------------------- *)
let rec scan_for_consts ast = 
  match ast with
  | ScmConst'(expr') -> [expr']
  | ScmIf'(test, dit, dif) -> scan_for_consts test @ scan_for_consts dit @ scan_for_consts dif
  | ScmSeq'(seq) -> List.flatten( List.map (fun e -> scan_for_consts e) seq )
  | ScmSet'(_, expr') -> scan_for_consts expr'
  | ScmDef'(_, expr') -> scan_for_consts expr'
  | ScmOr'(expr's) -> List.flatten( List.map (fun e -> scan_for_consts e) expr's)
  | ScmLambdaSimple'(_, expr') -> scan_for_consts expr'
  | ScmLambdaOpt'(_, _, expr') -> scan_for_consts expr'
  | ScmApplic'(expr', expr's) -> scan_for_consts expr' @ List.flatten( List.map (fun e -> scan_for_consts e) expr's )
  | ScmApplicTP'(expr', expr's) -> scan_for_consts expr' @ List.flatten( List.map (fun e -> scan_for_consts e) expr's )
  | ScmBoxSet'(_, expr') -> scan_for_consts expr'
  | _ -> [] (* no constants in this expressions: ScmVar, ScmBox', ScmBoxGet' *);;
  
let rec remove_duplicates lst res = 
  match lst with
  | [] -> res
  | (car :: cdr) -> if List.mem car res then remove_duplicates cdr res else remove_duplicates cdr (res @ [car]);;
  
let rec expand_sub_consts lst =
  match lst with
  | [] -> []
  | hd :: tl -> (
      match hd with
      | ScmNil -> expand_sub_consts tl
      | ScmVoid -> expand_sub_consts tl
      | ScmBoolean _ -> expand_sub_consts tl
      | ScmSymbol(s) -> [ScmString(s)] @ [hd] @ (expand_sub_consts tl)
      | ScmPair(car, cdr) -> (expand_sub_consts [car; cdr]) @ [hd] @ (expand_sub_consts tl)
      | ScmVector(v) -> (expand_sub_consts (List.map (fun e -> e) v)) @ [hd] @ (expand_sub_consts tl)
      | _ -> hd :: (expand_sub_consts tl)
    );;

let create_consts_table expanded_consts_lst = 
  let rec run lst index table = 
    match lst with
    | [] -> table
    | (hd :: tl) -> (
        match hd with
        | ScmNil -> run tl (index + 1) (table @ [ScmNil, (index, "MAKE_NIL")])
        | ScmVoid -> run tl (index + 1) (table @ [ScmVoid, (index, "MAKE_VOID")])
        | ScmBoolean(false) -> run tl (index + 2) (table @ [ScmBoolean(false), (index, "MAKE_BOOLEAN(0)")])
        | ScmBoolean(true) -> run tl (index + 2) (table @ [ScmBoolean(true), (index, "MAKE_BOOLEAN(1)")])
        | ScmChar(c) -> run tl (index + 2) (table @ [ScmChar(c), (index, "MAKE_LITERAL_CHAR(" ^ string_of_int(int_of_char c) ^ ")" )])
        | ScmNumber(ScmRational(n, d)) -> run tl (index + 9) (table @ [ScmNumber(ScmRational(n,d)), (index, "MAKE_LITERAL_RATIONAL(" ^ string_of_int n ^ ", " ^ string_of_int d ^ ")" )])
        | ScmNumber(ScmReal(r)) -> run tl (index + 1) (table @ [ScmNumber(ScmReal(r)), (index, "MAKE_LITERAL_FLOAT(" ^ (string_of_float r) ^ ")")])
        | ScmString(s) -> run tl (index + 1 + 8 + (String.length s)) (table @ [ScmString(s), (index, "MAKE_LITERAL_STRING(\"" ^ s ^ "\")")])
        | ScmSymbol(s) -> run tl (index + 1 + 8) (table @ [ScmSymbol(s), (index, "MAKE_LITERAL_SYMBOL(" ^ (string_of_int(find_const_index_in_table table (ScmString s)) ^ ")" ))])
      (* | ScmVector(v) -> run tl (index + 1 + 8 + (List.length v)) (table @ [ScmVector(v), (index, "db T_VECTOR")]) *)
        | ScmPair(car, cdr) -> run tl (index + 1 + 8 + 8) (table @ [ScmPair(car, cdr), (index, "MAKE_LITERAL_PAIR(consts_tbl + " ^ string_of_int(find_const_index_in_table table car) ^ ", consts_tbl + " ^ string_of_int(find_const_index_in_table table cdr) ^ ")" )])
      ) 
  in 
  run ([ScmNil; ScmVoid; ScmBoolean(false); ScmBoolean(true)] @ expanded_consts_lst) 0 [];;

let rec find_const_index_in_table table const = 
  match table with
  | [] -> -1
  | (hd :: tl) -> (
      match hd with
      | (const', (index, _ )) -> if const = const' then index else find_const_index_in_table tl const
    );;

let make_consts_tbl asts = 
    (* let a = [ScmConst'(ScmNil); ScmConst'(ScmSymbol("a")); ScmConst'(ScmBoolean (true)); ScmConst'(ScmBoolean (true))] in 
    let s1 = List.flatten (List.map scan_for_consts a) in 
    let s2 = remove_duplicates a [] in 
    let s3 = expand_sub_consts s2 in 
    let s4 = remove_duplicates s3 [] in 
    let s5 = create_consts_tbl s4
    s5 *)
  create_consts_table(
    remove_duplicates (
      expand_sub_consts (
        remove_duplicates (
          List.flatten (List.map scan_for_consts asts)) [])) []);;
(* -------------------------------------------- END OF CONSTS VARS TABLE IMPLEMENTATION -------------------------------------------- *)


(* ----------------------------------------- BEGINNING OF FREE VARS TABLE IMPLEMENTATION ----------------------------------------- *)
let rec scan_for_free_vars ast = 
  match ast with
  | ScmVar'(name) -> [name]
  | ScmIf'(test, dit, dif) -> (scan_for_free_vars test) @ (scan_for_free_vars dit) @ (scan_for_free_vars dif)
  | ScmSeq'(seq) -> List.flatten (List.map scan_for_free_vars seq)
  | ScmSet'(var, value) -> scan_for_free_vars (ScmVar' var) @ (scan_for_free_vars value)
  | ScmDef'(var, value) -> scan_for_free_vars (ScmVar' var) @ (scan_for_free_vars value)
  | ScmOr'(lst) -> List.flatten (List.map scan_for_free_vars lst)
  | ScmLambdaSimple'( _ , body) -> scan_for_free_vars body
  | ScmLambdaOpt'( _ , _ , body) -> scan_for_free_vars body
  | ScmApplic'(func, args) -> (scan_for_free_vars func) @ (List.flatten (List.map scan_for_free_vars args))
  | ScmApplicTP'(func, args) -> (scan_for_free_vars func) @ (List.flatten (List.map scan_for_free_vars args))
  | _ -> []

let rec create_fvars_table fvars_lst index = 
  (* fvars_lst example: ["+"; "car"; "cdr"; "length"; ... ; "foo"] *)
  match fvars_lst with
  | [] -> []
  | (hd :: tl) -> (hd , index) :: create_fvars_table tl (index + 1);;

let make_fvars_tbl asts = 
  create_fvars_table(
    remove_duplicates (
      List.flatten (List.map scan_for_free_vars asts)) 
      []) 0;;
(* ----------------------------------------- END OF FREE VARS TABLE IMPLEMENTATION ----------------------------------------- *)

  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

