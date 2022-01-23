(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
    (* pe = parsed expression *)
    (* I should send correct params and env to run function in recursion calls *)
   let rec run pe params env =
      match pe with
      | ScmConst value                  -> ScmConst' value (* DONE *)
      | ScmVar name                     -> ScmVar' (tag_lexical_address_for_var name params env) (* DONE *)
      | ScmIf (test, dit, dif)          -> ScmIf' ((run test params env), (run dit params env), (run dif params env)) (* DONE *)
      | ScmSeq es                       -> ScmSeq' (List.map (fun e -> run e params env) es) (* DONE *)
      | ScmSet (ScmVar(var), value)     -> ScmSet' (tag_lexical_address_for_var var params env, run value params env) (* DONE *)
      | ScmDef (ScmVar(var), value)     -> ScmDef' (tag_lexical_address_for_var var params env, run value params env) (* DONE *)
      | ScmOr exps                      -> ScmOr' (List.map (fun e -> run e params env) exps) (* DONE *)
      | ScmLambdaSimple (vars, body)    -> ScmLambdaSimple' (vars, run body vars ([params] @ env)) (* DONE *)
      | ScmLambdaOpt (vars, var, body)  -> ScmLambdaOpt' (vars, var, run body (var :: vars) ([params] @ env)) (* DONE *)
      | ScmApplic (f, args)             -> ScmApplic' (run f params env, List.map (fun e -> run e params env) args) (* DONE *)
      | _ -> raise X_this_should_not_happen
   in 
   run pe [] [];;


  (* returns a pair consists of: the first is items in the list except the last one, and the second is the last element of the list *)
  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
    let rec run pe in_tail =
     match pe with
       | ScmConst' value                  -> ScmConst' value (* DONE *)
       | ScmVar' name                     -> ScmVar' name (* DONE *)
       | ScmIf' (test, dit, dif)          -> ScmIf' ((run test false), (run dit in_tail), (run dif in_tail)) (* DONE *)
       | ScmSeq' exp                      -> let (except_last, last) = rdc_rac exp in ScmSeq' ((List.map (fun e -> run e false) except_last) @ [run last in_tail]) (* DONE *)
       | ScmSet' (var, value)             -> ScmSet' (var, (run value false)) (* DONE *)
       | ScmDef' (var, value)             -> ScmDef' (var, (run value false)) (* DONE *)
       | ScmOr' exps                      -> let (except_last, last) = rdc_rac exps in ScmOr' ((List.map (fun e -> run e false) except_last) @ [run last in_tail]) (* DONE *)
       | ScmLambdaSimple' (vars, body)    -> ScmLambdaSimple' (vars, run body true) (* DONE *)
       | ScmLambdaOpt' (vars, var, body)  -> ScmLambdaOpt' (vars, var, run body true) (* DONE *)
       | ScmApplic' (f, args)             -> if in_tail = true then ScmApplicTP' ((run f false), (List.map (fun e -> run e false ) args)) else ScmApplic' ((run f false), (List.map (fun e -> run e false ) args)) (* DONE *)
       | _ -> raise X_this_should_not_happen 
    in 
    run pe false;;

  (* boxing *)

  let find_reads name enclosing_lambda expr = raise X_not_yet_implemented 


  let rec box_set expr = 
    let rec recursion_box e = 
      match e with 
      | ScmBoxSet' (var, exp) -> ScmBoxSet' (var, recursion_box exp)
      | ScmIf'(test, dit, dif)-> ScmIf'(recursion_box test, recursion_box dit, recursion_box dif) 
      | ScmSeq' e_list -> ScmSeq' (List.map (fun exp -> recursion_box exp) e_list)
      | ScmSet' (v, exp) -> ScmSet' (v, recursion_box exp)
      | ScmDef' (v, exp) -> ScmDef' (v, recursion_box exp)
      | ScmOr' e_list -> ScmOr' (List.map (fun exp -> recursion_box exp) e_list)
      | ScmLambdaSimple' (elemnt, expr)  -> ScmLambdaSimple'(elemnt, remove_sequence (recursion_box (box_as elemnt expr [])))
      | ScmLambdaOpt' (elemnt, el_opt, expr) -> ScmLambdaOpt'(elemnt,el_opt, remove_sequence (recursion_box (box_as (elemnt@[el_opt]) expr [])))
      | ScmApplic' (proc, args) -> ScmApplic' (recursion_box proc, List.map (fun arg -> recursion_box arg) args)
      | ScmApplicTP' (proc, args) -> ScmApplicTP' (recursion_box proc, List.map (fun arg -> recursion_box arg) args)
      | _ -> e
         
    and elemnts_boxed expr e_to_box = 
      let n_exp = e_get_set e_to_box expr in
      let setsList = List.map (fun param -> e_to_add param expr) e_to_box in
      ScmSeq' (setsList@[recursion_box n_exp])

    and remove_sequence exp = 
    match exp with
    | ScmSeq' [e] -> e 
    |  _ -> exp  
       
  and e_get_set e_to_box expr  = 
    match e_to_box with
  | [] -> expr
  | car::cdr -> let expr_new = change_set_get car expr in e_get_set cdr expr_new 
     
  and box_no_box param expr = let (exp1,exp2,exp3) = look_out param expr (false,false,false) in
           (exp1 && exp2 && exp3)

    and box_as elemnt expr e_to_box = 
      match elemnt with
      | [] -> (elemnts_boxed expr e_to_box) 
      | car::cdr -> let is_e_box = box_no_box car expr in box_as cdr expr (if is_e_box  then (e_to_box@[car]) else e_to_box) 
                          

  
    and look_out elemnt e (exp1,exp2,exp3) = 
      match e with
      | ScmSet' (VarBound (par, _, _), exp) -> if par = elemnt then look_out elemnt exp (true,true,exp3) else look_out elemnt exp (exp1,exp2,exp3) 
      | ScmSet' (VarParam (par, _), exp) -> if par = elemnt then look_out elemnt exp (exp1,true,exp3) else look_out elemnt exp (exp1,exp2,exp3)(* set*)
      | ScmVar' (VarBound (par, _, _)) -> if par = elemnt then (true,exp2,true) else (exp1,exp2,exp3) 
      | ScmVar' (VarParam (par, _)) -> if par = elemnt then (exp1,exp2,true) else (exp1,exp2,exp3)  
      | ScmBoxSet' (_,exp) -> look_out elemnt exp (exp1,exp2,exp3)
      | ScmIf'(test, dit, dif)-> check_exp elemnt (test::dit::dif::[]) (exp1,exp2,exp3)
      | ScmSeq' se_list -> check_exp elemnt se_list (exp1,exp2,exp3)
      | ScmSet' (v, exp) -> look_out elemnt exp (exp1,exp2,exp3)
      | ScmDef' (v, exp) -> look_out elemnt exp (exp1,exp2,exp3)
      | ScmOr' e_list -> check_exp elemnt e_list (exp1,exp2,exp3)
      | ScmLambdaSimple' (e, exp)  ->  if List.mem elemnt e then (false,false,false) else look_out elemnt exp (exp1,exp2,exp3)
      | ScmLambdaOpt' (e, el_opt,exp) -> if List.mem elemnt e || List.mem elemnt [el_opt] then (false,false,false) else look_out elemnt exp (exp1,exp2,exp3)
      | ScmApplic' (proc, args) -> check_exp elemnt (proc::args) (exp1,exp2,exp3)
      | ScmApplicTP' (proc, args) ->  check_exp elemnt (proc::args) (exp1,exp2,exp3)
      | _ -> (exp1,exp2,exp3)
        
      
      and  max_in_list l x = 
      match l with
      | [] -> x
      | car::cdr -> let m = Pervasives.max x car in max_in_list cdr m

    and check_exp elemnt e_list (exp1,exp2,exp3) = 
      match e_list with
      | [] -> (exp1,exp2,exp3)
      | (car::cdr) -> let (n_exp1,n_exp2,n_exp3) = look_out elemnt car (exp1,exp2,exp3) in check_exp elemnt cdr (n_exp1,n_exp2,n_exp3)
  
                  
  and minor_to_apdate_set elemnt e = 
      match e with
      | ScmSet' (VarBound (p, _, min_index), _) -> if p = elemnt then min_index else (-1)
      | ScmSet' (VarParam (p, min_index), _) -> if p = elemnt then min_index else (-1)
      | ScmVar' (VarBound (p, _, min_index)) -> if p = elemnt then min_index else (-1)
      | ScmVar' (VarParam (p, min_index)) ->  if p = elemnt then min_index else (-1)
      | ScmBox' (VarParam (p, min_index)) -> if p = elemnt then min_index else (-1)
      | ScmBoxGet' bGet -> minor_to_apdate_set elemnt (ScmVar' bGet)
      | ScmBoxSet' (bSet,exp) -> max_in_list [(minor_to_apdate_set elemnt (ScmVar' bSet)) ; (minor_to_apdate_set elemnt exp)] (-1) 
      | ScmIf'(test, dit, dif)-> max_in_list [(minor_to_apdate_set elemnt test) ; (minor_to_apdate_set elemnt dit) ; (minor_to_apdate_set elemnt dif)] (-1)
      | ScmSeq' se_list -> max_in_list (List.map (fun exp -> minor_to_apdate_set elemnt exp) se_list) (-1)
      | ScmSet' (v, exp) -> max_in_list [(minor_to_apdate_set elemnt (ScmVar' v)) ; (minor_to_apdate_set elemnt exp)] (-1)
      | ScmDef' (v, exp) -> max_in_list [(minor_to_apdate_set elemnt (ScmVar' v)) ; (minor_to_apdate_set elemnt exp)] (-1)
      | ScmOr' e_list -> max_in_list (List.map (fun exp -> minor_to_apdate_set elemnt exp) e_list) (-1)
      | ScmLambdaSimple' (e, exp)  -> minor_to_apdate_set elemnt exp
      | ScmLambdaOpt' (e, el_opt,exp) -> minor_to_apdate_set elemnt exp
      | ScmApplic' (proc, args) |ScmApplicTP' (proc, args) -> max_in_list ((minor_to_apdate_set elemnt proc)::(List.map (fun arg -> minor_to_apdate_set elemnt arg) args)) (-1)
      | _ -> -1
          
    and e_to_add elemnt expr= 
      let minor = minor_to_apdate_set elemnt expr in
      let varParam = (VarParam (elemnt, minor)) in
      let add = ScmSet' (varParam, (ScmBox' varParam)) in
      add
  
  
    and change_set_get elemnt expr =  
      match expr with 
      | ScmSet' (VarBound (p, major_index, min_index), exp) -> if p = elemnt then ScmBoxSet' ((VarBound (p, major_index, min_index)), (change_set_get elemnt exp)) else ScmSet' (VarBound (p, major_index, min_index), (change_set_get elemnt exp))
      | ScmSet' (VarParam (p, min_index), exp) ->  if p = elemnt then ScmBoxSet' ((VarParam (p, min_index)), (change_set_get elemnt exp)) else ScmSet' ((VarParam (p, min_index)), (change_set_get elemnt exp))
      | ScmVar' (VarBound (p, major_index, min_index)) -> if p = elemnt then ScmBoxGet' (VarBound (p, major_index, min_index)) else expr
      | ScmVar' (VarParam (p, min_index)) -> if p = elemnt then ScmBoxGet' (VarParam (p, min_index)) else expr
      | ScmBoxSet' (v,exp) -> ScmBoxSet' (v ,(change_set_get elemnt exp)) 
      | ScmIf'(test, dit, dif)-> ScmIf' ((change_set_get elemnt test), (change_set_get elemnt dit), (change_set_get elemnt dif))
      | ScmSeq' se_list -> ScmSeq' (List.map (fun exp -> (change_set_get elemnt exp)) se_list)
      | ScmDef' (v, exp) -> ScmDef' (v, (change_set_get elemnt exp))
      | ScmOr' e_list -> ScmOr' (List.map (fun exp -> change_set_get elemnt exp) e_list)
      | ScmLambdaSimple' (e, exps)  -> if List.mem elemnt e then ScmLambdaSimple' (e, exps) else ScmLambdaSimple' (e, change_set_get elemnt exps)
      | ScmLambdaOpt' (e, el_opt,exps) -> if List.mem elemnt e || List.mem elemnt [el_opt] then ScmLambdaOpt' (e, el_opt, exps) else ScmLambdaOpt' (e, el_opt, change_set_get elemnt exps)
      | ScmApplic' (proc, args) -> ScmApplic' ((change_set_get elemnt proc) , List.map (fun arg -> (change_set_get elemnt arg)) args)
      | ScmApplicTP' (proc, args) -> ScmApplicTP' ((change_set_get elemnt proc) , List.map (fun arg -> (change_set_get elemnt arg)) args)
      | _ -> expr
         
    in recursion_box expr;;

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
