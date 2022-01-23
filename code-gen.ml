#use "semantic-analyser.ml";;

exception X_not_recognized_expression of expr'

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

let primitives = [  "+"; "*" ; "-"; "/"; 
                    "<"; "="; ">"; "eq?"; "equal?"; "not"; 
                    "zero?"; "boolean?"; "char?"; "integer?"; "list?"; "null?"; "pair?"; "procedure?"; "rational?"; "number?"; "flonum?"; "string?";
                    "append"; "apply"; "map"; "fold-right";"fold-left";
                    "car"; "cdr"; "length"; "list"; "cons"; "cons*";"set-car!"; "set-cdr!";
                    "char->integer";"numerator"; "denominator"; "gcd"; "integer->char"; "exact->inexact"; 
                    "make-string"; "string->list"; "string-length"; "string-ref"; "string-set!"; "symbol"; "symbol->string" ];;

let count = ref 1;;

let inc_and_update counter = 
  let c = !counter in 
  let _ = counter := !counter + 1 in
  c;;


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
  | _ -> [] (* no constants in this expressions: ScmVar', ScmBox', ScmBoxGet' *);;
  
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

let rec find_const_index_in_table table const = 
  match table with
  | [] -> -1
  | (hd :: tl) -> (
      match hd with
      | (const', (index, _ )) -> if const = const' then index else find_const_index_in_table tl const
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
        | ScmSymbol(s) -> run tl (index + 1 + 8) (table @ [ScmSymbol(s), (index, "MAKE_LITERAL_SYMBOL(" ^ string_of_int(find_const_index_in_table table (ScmString s)) ^ ")" )])
        | ScmVector(v) -> run tl (index + 1 + 8 + (List.length v)) (table @ [ScmVector(v), (index, "")])
        | ScmPair(car, cdr) -> run tl (index + 1 + 8 + 8) (table @ [ScmPair(car, cdr), (index, "MAKE_LITERAL_PAIR(consts_tbl + " ^ string_of_int(find_const_index_in_table table car) ^ ", consts_tbl + " ^ string_of_int(find_const_index_in_table table cdr) ^ ")" )])
      ) 
  in 
  run ([ScmNil; ScmVoid; ScmBoolean(false); ScmBoolean(true)] @ expanded_consts_lst) 0 [];; 

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
  | ScmVar'(VarFree(name)) -> [name]
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

let rec find_fvar_in_fvars_table fvars_tbl fvar = 
  match fvars_tbl with
  | [] -> -1
  | (hd :: tl) ->  (
      match hd with
      | (var, index) -> if (var = fvar) then index else find_fvar_in_fvars_table tl fvar 
    );;

let make_fvars_tbl asts = 
  create_fvars_table(
    remove_duplicates (
      List.flatten (List.map scan_for_free_vars asts))
      ([] @ primitives)) 0;;
(* ----------------------------------------- END OF FREE VARS TABLE IMPLEMENTATION ----------------------------------------- *)


(* ----------------------------------------- BEGINNING OF GENERATE FUNCTION IMPLEMENTATION ----------------------------------------- *)

let imp_macro n c= Printf.sprintf "mov rbx, [rsp + 8*3]
cmp rbx, %d
je e%dquals_
cmp rbx, %d
jl l%desser_
R%dgreaters_:
lea rcx, [rbx - %d] ;; difference, length of the list
lea rdx, [rsp + 8*(3+rbx)]
mov rsi, [rdx]
MAKE_PAIR(rax,rsi,SOB_NIL_ADDRESS)
sub rdx, 8
g%dreatloop_:
cmp rcx, 0
je g%dreatend_
mov rsi, [rdx]
push rbx
mov rbx, rax
MAKE_PAIR(rax,rsi,rbx)
pop rbx
sub rdx, 8
dec rcx
jmp g%dreatloop_
g%dreatend_:
mov [rsp + 8*(3+rbx)], rax
lea rax, [rsp+8*(2+rbx)]
lea rcx, [3 + %d]
m%doveloop_:
mov rdx, [rsp + 8*(rcx-1)]
mov [rax], rdx
sub rax, 8
dec rcx
cmp rcx, 0
  jne m%doveloop_
           lea rcx, [rbx - %d]
  lea rbx ,[8*rcx]
  add rsp, rbx
  sub [rsp + 8* 3], rcx
  jmp e%dnd_opt_
                      l%desser_:
                      lea rax, [4+rbx]
  mov rcx, 0
  l%dessloop_:
             cmp rax, 0
  je w%drapit_
                        mov rdx, [rsp + (8*rcx)]
  mov [rsp + 8*rcx - 8], rdx
  dec rax
  inc rcx
  jmp l%dessloop_
                           w%drapit_:
                           sub rsp, 8
  mov rax, SOB_NIL_ADDRESS
  mov [rsp + 8*(4 + rbx)], rax
  add qword [rsp + 8*3], 1
  jmp e%dnd_opt_
                           e%dquals_:
                           mov rcx, [rsp + 8*(3+rbx)]
  MAKE_PAIR(rax, rcx, SOB_NIL_ADDRESS)
  mov [rsp + 8*(3+rbx)], rax
  e%dnd_opt_:" n c n c c n c c c c n c c n c c c c c c c c c 
let string_of_float_ flt =
  let str = string_of_float flt in
  let ch = String.get str ((String.length str) -1)  in
  if (ch = '.') then (str^"0") else str

let rec generate_helper consts fvars env exp = 
  match exp with
  (* Constants *)
  | ScmConst'(c) -> "mov rax, " ^ string_of_int(find_const_index_in_table consts c) ^ "\n"
  (* Parameters: get, set *)
  | ScmVar'(VarParam( _ , minor)) -> "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int minor ^ "] \n"
  | ScmSet'(VarParam( _ , minor ), value) -> generate_helper consts fvars env value ^ 
                                             "mov qword [rbp + 8 * (4 + " ^ string_of_int minor ^ ")], rax\n
                                             mov rax, SOB_VOID_ADDRESS \n"
  (* Bound Vars: get, set *)
  | ScmVar'(VarBound( _ , major, minor)) -> "mov rax, qword [rbp + 8 * 2] \n
                                            mov rax, qword [rax + 8 * " ^ string_of_int major ^ "] \n
                                            mov rax, qword [rax + 8 * " ^ string_of_int minor ^ "] \n"
  | ScmSet'(VarBound( _ , major, minor ), value) -> generate_helper consts fvars env value ^ 
                                                    "mov rbx, qword[rbp + 8 * 2] \n
                                                    mov rbx, qword [rbx + 8 * " ^ string_of_int major ^ "] \n
                                                    mov qword [rbx + 8 * " ^ string_of_int minor ^ "], rax \n
                                                    mov rax, SOB_VOID_ADDRESS \n"
  (* Free Vars: get, set *)
  | ScmVar'(VarFree(v)) -> "mov rax, qword FVAR(" ^ string_of_int (find_fvar_in_fvars_table fvars v) ^ ")\n"
  | ScmSet'(VarFree(v), value) -> generate_helper consts fvars env value ^ 
                                  "mov qword [" ^ string_of_int (find_fvar_in_fvars_table fvars v) ^ "], rax \n
                                  mov rax, SOB_VOID_ADDRESS \n"
  (* Define *)
  | ScmDef'(var, value) -> generate_helper consts fvars env (ScmSet'(var, value))
  (* Sequences *)
  | ScmSeq'(seq) -> generate_sequence consts fvars env seq ^ "\n"
  (* Or *)
  | ScmOr'(exprs) -> generate_or consts fvars env exprs ^ "\n"
  (* If *)
  | ScmIf'(test, dit, dif) -> let c = inc_and_update count in
      generate_helper consts fvars env test ^ 
      "\ncmp rax, SOB_FALSE_ADDRESS \n" ^ 
      "je Lelse" ^ string_of_int c ^ "\n" ^ 
      generate_helper consts fvars env dit ^ "\n
                              jmp Lexit \n
                              Lelse" ^ string_of_int c ^ ":\n" ^ 
      generate_helper consts fvars env dif ^ "Lexit" ^ string_of_int c ^ ":\n"
  (* Boxes: ScmBoxGet' and ScmBoxSet' *)
  | ScmBoxGet'(var) -> generate_helper consts fvars env (ScmVar'(var)) ^ "\nmov rax, qword[rax]\n"
  | ScmBoxSet'(var, value) -> generate_helper consts fvars env value ^ "\npush rax\n" ^ 
                              generate_helper consts fvars env (ScmVar'(var)) ^ 
                              "\n pop qword[rax] \n
                              mov rax, SOB_VOID_ADDRESS \n"
  (* Lambdas: ScmLambdaSimple' and ScmLambdaOpt' *)
  | ScmLambdaSimple'(args, body) -> let c = inc_and_update count in
      (Printf.sprintf ";lambda simple\n\t%s\n%s" (lambdaenv c (env + 1)) (lambdaBody consts fvars body c (env + 1)))
  | ScmLambdaOpt'(args, body, body_opt) ->  let c = inc_and_update count in
      (Printf.sprintf ";lambda opt\n%s\n\n\n\n\n\n%s" (lambdaenv c (env + 1)) (lambdaBodyopt  consts fvars body_opt c (env + 1) (1+ (List.length args))))
  (* Applications *)
  | ScmApplic'(func, args) -> let proc = (generate_helper consts fvars env func) in 
      let n = List.length args in 
      (Printf.sprintf
         ";applic\n\t\t%s%s\n\tpush %d\n\tCLOSURE_ENV rsi, rax\n\tpush rsi\n\tCLOSURE_CODE rdx, rax\n\tcall rdx\n\tadd rsp, 8*1\n\tpop rbx\n\tshl rbx, 3\n\tadd rsp, rbx"
         (String.concat "" (List.map (fun v -> (Printf.sprintf "%s\n\tpush rax\n\t" (generate_helper consts fvars env v))) (List.rev args))) proc n)

  | ScmApplicTP'(func, args) -> generate_helper consts fvars env (ScmApplic'(func, args))
  | _ -> raise (X_not_recognized_expression exp)


and generate_sequence consts fvars env seq =
  match seq with
  | [] -> "\n"
  | (hd :: tl) -> generate_helper consts fvars env hd ^ "\n" ^ generate_sequence consts fvars env tl

and generate_or consts fvars env exp =
  let c = inc_and_update count in
  match exp with
  | [] -> "Lexit" ^ string_of_int c ^ ":\n"
  | (hd :: []) -> generate_helper consts fvars env hd ^ "\n" ^ generate_or consts fvars env []
  | (hd :: tl) -> generate_helper consts fvars env hd ^ "\ncmp rax, SOB_FALSE_ADDRESS \njne Lexit" ^ string_of_int c ^ "\n" ^ generate_or consts fvars env tl ^ "\n"

and lambdaenv c env = let env1 = Printf.sprintf "\n\t;lambda env\n\n\tMALLOC rax, WORD_SIZE*%d\n\tmov rbx, qword[rbp + 8 * 2]\n\tmov rcx, %d\nloop%d:\n\tcmp rcx, 0\n\tje endd%d\n\tmov rdx, qword[rbx + 8*(rcx-1)]\n\tmov [rax + 8*rcx], rdx\n\tdec rcx\n\tjmp loop%d\nendd%d:" env (env-1) c c c c in
  let env2 =  Printf.sprintf "mov rcx, [rbp + 8 * 3]\n\tpush rcx\n\tlea rcx, [rcx*WORD_SIZE]\n\tMALLOC rbx, rcx\n\tpop rcx\n\tmov [rax], rbx\nparamloop%d:\n\tcmp rcx, 0\n\tje end%d\n\tmov rdx, [rbp + 8*(3+rcx)]\n\tmov qword[rbx + 8*(rcx-1)], rdx\n\tdec rcx\n\tjmp paramloop%d\nend%d:" c c c c in
  Printf.sprintf "%s\n\t%s\n\tmov rbx, rax\n\tMAKE_CLOSURE(rax, rbx, Lbody%d)\n\tjmp Lcont%d" env1 env2 c c

and lambdaBody consts fvars body count env = Printf.sprintf "; Lambda body\nLbody%d:\n\tpush rbp\n\tmov rbp, rsp\n%s\n\tpop rbp\n\tret\nLcont%d:" count (generate_helper consts fvars env body) count

and lambdaBodyopt consts fvars body count env n = let opt_macro = imp_macro n count in Printf.sprintf ";lambda body\nLbody%d:\n\tpush rbp\n\t%s\n\tmov rbp, rsp\n%s\n\tpop rbp\n\tret\nLcont%d:" count opt_macro (generate_helper consts fvars env body) count ;;

let generate consts fvars e = generate_helper consts fvars 0 e;;
(* ----------------------------------------- END OF GENERATE FUNCTION IMPLEMENTATION ----------------------------------------- *)

end;;

