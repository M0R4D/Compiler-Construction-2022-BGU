#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec is_proper_list = function
  | ScmNil -> true
  | ScmPair(car, cdr) -> is_proper_list(cdr)
  | _ -> false;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"));;

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec symbols_list_to_string_list = function
| [] -> []
| ScmSymbol(s)::tl -> s::(symbols_list_to_string_list tl)
| _ -> raise (X_syntax_error (ScmNil, ""));;


let rec scm_improper_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_improper_list_to_list tl)
| ScmNil -> raise (X_syntax_error (ScmNil, "Expected improper list"))
| last -> [last]

let rec remove_list_last_element = function
  | hd::[] -> [] 
  | hd::tl -> hd::(remove_list_last_element tl) 
  | _ -> raise (X_syntax_error (ScmNil, ""))

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val macro_expand : sexpr -> sexpr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
  let sexpr = macro_expand sexpr in
  match sexpr with 
(* Implement tag parsing here *)

(* Conatants: *)
(* NULL *)
  | ScmNil -> ScmConst (ScmNil) 
(* Booleans *)
  | ScmBoolean(bool) -> ScmConst (ScmBoolean bool)
(* Characters *)
  | ScmChar(ch) -> ScmConst (ScmChar ch)
(* Numbers: (Rational, Real) *)
  | ScmNumber(num) -> ScmConst (ScmNumber num)
(* Strins *)
  | ScmString(str) -> ScmConst (ScmString str)
(* Qouted Expressions *)
  | ((ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)))) -> ScmConst x

(* Variables *)
  | ScmSymbol(symbol) -> if (List.mem symbol reserved_word_list) then 
        (raise (X_reserved_word symbol))
      else ScmVar (symbol)

(* Conditionals: (if test then else) , (if test then void)  *)
  | ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) -> 
      ScmIf (tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
  | ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) -> 
      ScmIf (tag_parse_expression test, tag_parse_expression dit, ScmConst (ScmVoid))

(* Disjunctions: (or) , (or <one-exp>), (or <exp1> <exp2> ... <expn>) *)
  | ScmPair(ScmSymbol("or"), ScmNil) -> ScmConst (ScmBoolean false)
  | ScmPair(ScmSymbol("or"), ScmPair(exp, ScmNil)) -> tag_parse_expression exp
  | ScmPair(ScmSymbol("or"), exps) -> ScmOr (List.map tag_parse_expression (scm_list_to_list exps))

(* Lambda Expressions: Simple lambda, Optional lambda, Variadic lambda *)
  | ScmPair(ScmSymbol("lambda"), ScmPair(args, body)) -> 
      lambda_maker args body

(* Define: Simple define, MIT-style define *)
  | ScmPair(ScmSymbol("define"), ScmPair(ScmSymbol(var), ScmPair(body, ScmNil))) ->
      if (List.mem var reserved_word_list) then
        raise (X_reserved_word var)
      else
        ScmDef (ScmVar var, tag_parse_expression body)
  | ScmPair(ScmSymbol("define"), ScmPair(ScmPair(ScmSymbol(var), args), body)) -> 
      ScmDef(ScmVar var, lambda_maker args body)

(* Assignments: set! operator *)
  | ScmPair(ScmSymbol("set!"), ScmPair(ScmSymbol(var), ScmPair(body, ScmNil))) -> ScmSet (ScmVar var, tag_parse_expression body)
  | ScmPair(ScmSymbol("set!"), ScmPair(_, body)) -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!"))
    (* match var with
      | ScmSymbol(var) -> 
      | _ -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!")) *)

(* Sequences: (begin) , (begin <one-exp>), (begin <exp1> <exp2> ... <expn>) *)
  | ScmPair(ScmSymbol("begin"), ScmNil) -> ScmConst (ScmVoid) (* begin without any expressions *)
  | ScmPair(ScmSymbol("begin"), ScmPair(exp1, ScmNil)) -> tag_parse_expression exp1 (* begin with one expression *)
  | ScmPair(ScmSymbol("begin"), body) -> ScmSeq(List.map (fun e -> tag_parse_expression e) (scm_list_to_list body)) (* begin with multiple expressions *)

(* Applications *)
  | ScmPair(ScmSymbol(name), ScmNil) -> ScmApplic (ScmVar name, []) 
  | ScmPair(app, args) -> 
      (match app with 
        | ScmSymbol(app) -> if (List.mem app reserved_word_list) then
              raise (X_reserved_word app)
            else
              ScmApplic (ScmVar app, List.map (fun e -> tag_parse_expression e) (scm_list_to_list args))
        | _ -> ScmApplic (tag_parse_expression app, List.map (fun e -> tag_parse_expression e) (scm_list_to_list args)))


(* Error: this should not happen *)
  | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and lambda_maker args body = 
  if is_proper_list args then simple_lambda_maker args body
  else match args with 
    | ScmSymbol(symbol) -> variadic_lambda_maker symbol body
    | _ -> optional_lambda_maker args body

and simple_lambda_maker args body = 
  try ScmLambdaSimple (symbols_list_to_string_list (scm_list_to_list args), body_maker body) with X_syntax_error(_, _) -> raise (X_syntax_error (args, "Error"))
and optional_lambda_maker args body = 
  let vars = symbols_list_to_string_list (scm_improper_list_to_list args) in 
  let var = List.nth vars ((List.length vars) - 1) in
  let vars = remove_list_last_element vars in
  ScmLambdaOpt (vars, var, body_maker body) 
and variadic_lambda_maker symbol body = 
  ScmLambdaOpt ([], symbol, body_maker body)

and body_maker body = 
  match body with
  | ScmPair(b , ScmNil) -> tag_parse_expression b
  | _ -> ScmSeq(List.map (fun e -> tag_parse_expression e) (scm_list_to_list body))


and macro_expand sexpr =
  match sexpr with
(* Handle macro expansion patterns here *)

(* Conjunctions *)
  | ScmPair(ScmSymbol("and"), args) -> macro_expansion_and args

(* Expansion for: let, let*, letrec *)
  | ScmPair(ScmSymbol("let"), ScmPair(ribs, body)) -> macro_expansion_let ribs body
  | ScmPair(ScmSymbol("let*"), ScmPair(ribs, body)) -> macro_expansion_let_star ribs body
  | ScmPair(ScmSymbol("letrec"), ScmPair(ribs, body)) -> macro_expansion_letrec ribs body

(* Expansion for: cond *)
  | ScmPair(ScmSymbol("cond"), ScmPair(ribs, body)) -> macro_expansion_cond ribs body

(* Expansion for QuasiQuotes: quasiquote, unquote, unquote-splicing *)
  | ScmPair(ScmSymbol("quasiquote"), ScmPair(exp, ScmNil)) -> macro_expansion_quasiquote exp

  | _ -> sexpr

and macro_expansion_and args = 
(*  {(and)} = {#t} (by definition)
    {(and ⟨expr⟩)} = {⟨expr⟩} (#t is the unit element of and)
    {(and ⟨expr1⟩ ⟨expr2⟩ · · · ⟨exprn⟩)} =(if {⟨expr1⟩} {(and ⟨expr2⟩ · · · ⟨exprn⟩)} {#f}) *)
  match args with
  | ScmNil -> ScmBoolean true
  | ScmPair(exp, ScmNil) -> exp
  | ScmPair(first, rest) -> ScmPair(ScmSymbol("if"), ScmPair((macro_expand first), ScmPair(macro_expansion_and rest, ScmPair(ScmBoolean(false), ScmNil))))
  | _ -> raise (X_syntax_error(args, "and pattern not recognized"))

and macro_expansion_let ribs body =
(* {(let ((var1 expr1) (var2 expr2) · · · (varn exprn)) body)} = {((lambda (var1 var2 · · · varn) body) expr1 expr2 · · · exprn} *)
  ScmPair(ScmPair(ScmSymbol "lambda" , ScmPair(let_vars_helper ribs, macro_expand body)), let_exprs_helper ribs)

and let_vars_helper ribs = 
  match ribs with
  | ScmNil -> ScmNil
  | ScmPair(ScmPair(ScmSymbol(var), ScmPair( _ , ScmNil)), rest) -> ScmPair(ScmSymbol(var), let_vars_helper rest)

and let_exprs_helper ribs = 
  match ribs with
  | ScmNil -> ScmNil
  | ScmPair(ScmPair( _ , ScmPair(exp, ScmNil)), rest) -> ScmPair(exp, let_exprs_helper rest)

and macro_expansion_let_star ribs body =
(* {(let* ((var1 expr1) (var2 expr2) · · · (varn exprn)) body)} = 
    = ( (lambda (var1) 
            (lambda (var2) 
            · · · (lambda (varn) body) exprn) exprn-1) · · · ) expr1) *)
  match ribs with
  | ScmNil -> macro_expand(ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))
  | ScmPair(rib1 , ScmNil) -> macro_expand(ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib1 , ScmNil), body)))
  | ScmPair(rib1, rest) -> macro_expand(ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib1, ScmNil), ScmPair (ScmPair (ScmSymbol "let*", ScmPair (rest, body)), ScmNil))))
  | _ -> ScmNil

and macro_expansion_letrec ribs body =
(* match ribs with
(* | ScmNil -> macro_expand(ScmPair(ScmSymbol "let",ScmPair(ScmNil, ScmPair(ScmPair(ScmSymbol "let", ScmPair(ScmNil, body)), ScmNil)))) *)
| ScmNil -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(ScmNil, ScmPair (body, ScmNil))))
(* | ScmNil -> macro_expand(ScmPair(ScmSymbol "let",ScmPair(ScmNil, ScmPair(ScmPair(ScmSymbol "let", ScmPair(ScmNil, ScmPair(body, ScmNil))), ScmNil)))) *)
| ScmPair(rib1, rest) -> ScmNil *)

(* second try *)
  let vars = List.map 
      (fun arg -> (match arg with
            | ScmPair(ScmSymbol(str),value) ->  ScmSymbol(str)
            | _ -> raise (X_syntax_error(arg, "error")))) 
      (scm_list_to_list ribs) in
  let n_var = list_to_proper_list (List.map (fun var -> ScmPair(var,ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil))) vars) in
  let vals = List.map 
      (fun arg -> (match arg with
            | ScmPair(ScmSymbol(str),value) -> value
            | _ -> raise (X_syntax_error(arg, "error")))) 
      (scm_list_to_list ribs) in
  let values = scm_zip 
      (fun var value -> ScmPair(ScmSymbol("set!"), ScmPair(var,(macro_expand value)))) 
      (list_to_proper_list vars) 
      (list_to_proper_list vals) in
  macro_expand (ScmPair(ScmSymbol("let"),ScmPair(n_var,(scm_append values body))))

and macro_expansion_cond ribs body = 
  match ribs with
  | ScmPair(rib, ScmPair(ScmSymbol("=>"), b)) -> expand_cond_arrow_rib rib b body
  | ScmPair(test, dit) -> expand_cond_rib test dit body
  | _ ->body

and expand_cond_rib test dit rest =
  match rest with
  | ScmNil -> (
      match test with 
      | ScmSymbol("else") -> (parse_rib dit)
      | _ -> (ScmPair(ScmSymbol("if"), ScmPair(test,ScmPair((parse_rib dit),ScmNil)))))
  | _ -> (
      match test with
      | ScmSymbol("else") -> (parse_rib dit)
      | _ -> (ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(
          (match (List.length (scm_list_to_list (macro_expand dit))) with
            | 1 -> List.hd (scm_list_to_list (macro_expand dit))
            | _ -> ScmPair(ScmSymbol("begin"),(macro_expand dit)))
        ,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))))))

and parse_rib rib = 
  (match (List.length (scm_list_to_list (macro_expand rib))) with
    | 0 -> raise (X_syntax_error(rib,"wrong syntax"))
    | 1 ->  (macro_expand (List.hd (scm_list_to_list (rib))))
    | _ -> ScmPair(ScmSymbol("begin"), (macro_expand rib)))

and expand_cond_arrow_rib test body rest = 
  match rest with
  | ScmNil -> (macro_expand (ScmPair(ScmSymbol("let"),
                                      (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
                                                      ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ScmPair(body,ScmNil))),ScmNil)),
                                                              ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil))), ScmPair(ScmPair(ScmSymbol("if"),
                                                                                                                                    ScmPair(ScmSymbol("value"), ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
                                                                                                                                                                        ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil))))))
  | _ -> (macro_expand (ScmPair(ScmSymbol("let"),
                                (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
                                                  ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand body))),ScmNil)),
                                                          ScmPair(ScmPair(ScmSymbol("rest"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))),ScmNil)),ScmNil))),
                                          ScmPair(ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"),
                                                                                  ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
                                                                                          ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil))))))

  
and macro_expansion_quasiquote rest =
  match rest with
  | ScmPair(ScmSymbol ("unquote"), ScmPair(xp, ScmNil)) -> xp
  | ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
  | ScmSymbol(_)-> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
  | ScmVector(list_rest) -> ScmPair(ScmSymbol "list->vector", ScmPair((macro_expansion_quasiquote (list_to_proper_list list_rest)), ScmNil))
  | ScmPair(ScmSymbol ("unquote-splicing"), ScmPair(_, ScmNil)) -> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
  | ScmPair((ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(xp, ScmNil)))), xp2) -> 
      (ScmPair((ScmSymbol("append")),(ScmPair(xp, (ScmPair((macro_expansion_quasiquote xp2), ScmNil))))))
  | ScmPair(xp, (ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(xp2, ScmNil))))) ->
      (ScmPair((ScmSymbol("cons")), (ScmPair((macro_expansion_quasiquote xp), (ScmPair(xp2, ScmNil))))))
  | ScmPair(xp, xp2) -> (ScmPair((ScmSymbol("cons")), (ScmPair((macro_expansion_quasiquote xp), (ScmPair((macro_expansion_quasiquote xp2), ScmNil))))))
  | _ -> rest


  
end;; 
