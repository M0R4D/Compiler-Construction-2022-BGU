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
    | ScmConst'(c) -> [c]
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
          | ScmString(s) -> run tl (index + 1 + 8 + (String.length s)) (table @ [ScmString(s), (index, "MAKE_LITERAL_STRING "^(string_of_int(String.length s))^",\" "^ s ^ "\"")])
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

  let string_of_float_ flt =
    let str = string_of_float flt in
    let ch = String.get str ((String.length str) -1)  in
    if (ch = '.') then (str^"0") else str

  let rec generate_helper consts fvars env exp = 
    match exp with
  (* Constants *)
    | ScmConst'(c) -> "mov rax, const_tbl + " ^ string_of_int(find_const_index_in_table consts c) ^ "\n"
  (* Parameters: get, set *)
    | ScmVar'(VarParam( _ , minor)) -> "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int minor ^ ")] \n"
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
    | ScmVar'(VarFree(v)) -> "mov rax, qword[fvar_tbl + " ^ string_of_int (find_fvar_in_fvars_table fvars v) ^ "]\n"
    | ScmSet'(VarFree(v), value) -> generate_helper consts fvars env value ^ 
                                    "mov qword [fvar_tbl + " ^ string_of_int (find_fvar_in_fvars_table fvars v) ^ "], rax \n
                                  mov rax, SOB_VOID_ADDRESS \n"
  (* Define *)
    (* | ScmDef'(var, value) -> generate_helper consts fvars env (ScmSet'(var, value)) *)
    | ScmDef'(VarFree(var), value) -> generate_helper consts fvars env value ^ 
                            "mov qword [fvar_tbl + " ^ string_of_int (find_fvar_in_fvars_table fvars var) ^ "], rax \n
                            mov rax, SOB_VOID_ADDRESS \n"
  (* Sequences *)
    | ScmSeq'(seq) -> (List.fold_left(fun acc expr-> acc ^ (generate_helper consts fvars env expr) ^ "\n") "" seq)
  (* Or *)
    | ScmOr'(exprs) ->let c = inc_and_update count in
                 generate_or consts fvars env exprs c ^ "\n"
  (* If *)
    | ScmIf'(test, dit, dif) -> let c = inc_and_update count in
        generate_helper consts fvars env test ^ 
        "\ncmp rax, SOB_FALSE_ADDRESS \n" ^ 
        "je Lelse" ^ string_of_int c ^ "\n" ^ 
        generate_helper consts fvars env dit ^ "\n
                              jmp Lexit"^ string_of_int c ^"\n
                              Lelse" ^ string_of_int c ^ ":\n" ^ 
        generate_helper consts fvars env dif ^ "Lexit" ^ string_of_int c ^ ":\n"
  (* Boxes: ScmBoxGet' and ScmBoxSet' *)
    | ScmBox'(VarParam( _ , minor)) -> 
                                    ";box to string\nmov rax, qword[rbp + 8 * (4 + " ^ string_of_int minor ^ ")]\n" ^
                                    "push SOB_NIL_ADDRESS ; something for the cdr\n" ^
                                    "push rax             ; car\n" ^
                                    "push 2               ; argc\n" ^
                                    "push SOB_NIL_ADDRESS ;fake env\n" ^
                                    "call cons\n" ^
                                    "add rsp,8*1          ;pop env\n" ^
                                    "pop rbx              ;pop argc\n" ^
                                    "shl rbx,3            ;rbx=rbx*8\n" ^
                                    "add rsp,rbx          ;pop args\n" ^
                                    "mov qword[rbp + 8 * (4 + " ^ string_of_int minor ^ ")],rax\n"
    | ScmBoxGet'(var) -> generate_helper consts fvars env (ScmVar'(var)) ^ "\nmov rax, qword[rax]\n"
    | ScmBoxSet'(var, value) -> generate_helper consts fvars env value ^ "\npush rax\n" ^ 
                                generate_helper consts fvars env (ScmVar'(var)) ^ 
                                "\n pop qword[rax] \n
                              mov rax, SOB_VOID_ADDRESS \n"
  (* Lambdas: ScmLambdaSimple' and ScmLambdaOpt' *)
    | ScmLambdaSimple'(args, body) -> let c = inc_and_update count in
                                      let lcode = "Lcode" ^ (string_of_int c) in 
                                      let lcont = "Lcont" ^ (string_of_int c) in
                                      ";lambda expr\nMAKE_ENV " ^ (string_of_int env) ^ 
                                      "\nmov rbx, rax\n"^
                                      "MAKE_CLOSURE(rax, rbx, "  ^ lcode ^ ")\n"^
                                      "jmp " ^ lcont ^ "\n" ^
                                      lcode ^ ":\n" ^
                                      "push rbp\n" ^
                                      "mov rbp, rsp\n" ^
                                      generate_helper consts fvars (env + 1) body ^
                                      "leave\n" ^
                                      "ret\n" ^
                                      lcont ^ ":\n"
    | ScmLambdaOpt'(args, opt, body) ->  let c = inc_and_update count in
                                          let lcode = "Lcode" ^ (string_of_int c) in 
                                          let lcont = "Lcont" ^ (string_of_int c) in
                                          let num_of_desired_args = (string_of_int ((List.length args) + 1)) in
                                          ";lambda optional\nMAKE_ENV " ^ (string_of_int env) ^ 
                                          "\nmov rbx, rax\n"^
                                          "MAKE_CLOSURE(rax, rbx, "  ^ lcode ^ ")\n"^
                                          "jmp " ^ lcont ^ "\n" ^
                                          lcode ^ ":\n" ^ 
                                          "CHANGE_STACK_OF_LAMBDA_OPT " ^ num_of_desired_args ^"\n" ^
                                          "push rbp\n" ^
                                          "mov rbp, rsp\n" ^
                                          generate_helper consts fvars (env + 1) body ^
                                          "leave\n" ^
                                          "ret\n" ^
                                          lcont ^ ":\n"
  (* Applications *)
    | ScmApplic'(func, args) -> let n = string_of_int (List.length args) in
                                let push_args_code = List.fold_right (fun arg acc-> acc ^ (generate_helper consts fvars env arg) ^ "push rax\n")  args "" in
                                ";application exp to string\n" ^ push_args_code ^ 
                                "push " ^ n ^ "\n" ^
                                (generate_helper consts fvars env func) ^
                                "CLOSURE_ENV rbx, rax\n" ^
                                "push rbx\n" ^
                                "CLOSURE_CODE rbx, rax\n" ^
                                "call rbx\n" ^
                                "add rsp,8*1 ;pop env\n" ^
                                "pop rbx     ;pop arg count\n" ^
                                "shl rbx,3   ;rbx = rbx*8\n" ^
                                "add rsp,rbx ;pop args\n"
    | ScmApplicTP'(func, args) -> let n = string_of_int (List.length args) in
                                  let push_args_code = List.fold_right (fun arg acc-> acc ^ (generate_helper consts fvars env arg) ^ "push rax\n")  args "" in
                                  ";applicTP exp to string\n" ^ push_args_code ^ 
                                  "push " ^ n ^ "\n" ^
                                  (generate_helper consts fvars env func) ^
                                  "CLOSURE_ENV rbx, rax\n" ^
                                  "push rbx\n" ^
                                  "push qword[rbp + 8 * 1] ;old ret addr\n" ^
                                  "CHANGE_APPLICTP_STACK " ^ (string_of_int (3 + (List.length args))) ^ "\n" ^
                                  "CLOSURE_CODE rbx, rax\n" ^
                                  "jmp rbx\n"
    | _ -> raise (X_not_recognized_expression exp)


  (* and generate_sequence consts fvars env seq =
    match seq with
    | (hd :: tl) -> generate_helper consts fvars env hd ^ "\n" ^ generate_sequence consts fvars env tl
    |_->"\n" *)

  and generate_or consts fvars env exp c =
    match exp with
    | [] -> "Lexit" ^ string_of_int c ^ ":\n"
    | (hd :: []) -> generate_helper consts fvars env hd ^ "\n" ^ generate_or consts fvars env [] c
    | (hd :: tl) -> generate_helper consts fvars env hd ^ "\ncmp rax, SOB_FALSE_ADDRESS \njne Lexit" ^ string_of_int c ^ "\n" ^ generate_or consts fvars env tl c ^ "\n"

  
  let generate consts fvars e = generate_helper consts fvars 0 e;;
(* ----------------------------------------- END OF GENERATE FUNCTION IMPLEMENTATION ----------------------------------------- *)

end;;

