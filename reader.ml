(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

type standart_or_interpolated =
  | Static of string
  | Dynamic of sexpr

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str

and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
  
and nt_line_comment str = 
  unitify ( caten (word ";") (caten (star (diff nt_any nt_end_of_line_or_file)) (nt_end_of_line_or_file))) str

and nt_paired_comment str = 
  let nt1 = disj_list [unitify nt_char; unitify nt_string; unitify nt_comment] in 
  let nt2 = disj nt1 (unitify (one_of "{}")) in 
  let nt3 = diff (unitify nt_any) nt2 in
  let nt4 = star (disj nt3 nt1) in
  let nt5 = unitify (caten (char '{') (caten nt4 (char '}'))) in
  nt5 str

and nt_sexpr_comment str = 
  unitify (caten (word "#;") nt_sexpr) str

and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str

and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str

and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1

(* ------------------------------- *)
and nt_expon_token str= disj_list [(word_ci "e");(word "*10^");(word "*10**")] str
 
and nt_natural str = 
  let rec nt str =  pack (caten nt_digit_0_9 (disj nt nt_epsilon)) 
      (function (a,s) -> a::s) str in
  pack nt (fun s-> List.fold_left (fun a b -> 10*a+b) 0 s) str
     
and nt_plus_or_minus str = maybe (disj (char '+') (char '-')) str
 
and nt_integer str =
  let nt1 =  pack (not_followed_by (caten nt_plus_or_minus nt_natural) nt_symbol_char) (fun (cnst, num) -> match cnst with
      |Some ('-') -> num* (-1)
      |Some ('+') -> num
      |None -> num
      | _ -> num) in
  nt1 str
and nt_int str = 
  let nt1 = pack nt_integer (fun x -> match x with
      | x -> ScmNumber (ScmRational(x,1))) in
  nt1 str
     
and nt_frac str =
  let nt1 = caten nt_integer (caten (char '/') nt_natural) in
  let nt1  = pack nt1 (fun (num, (sign, den)) -> ScmNumber
                          (ScmRational (num/gcd num den,den/gcd num den))) in
  nt1 str
 
and nt_integer_part str = nt_natural str
 
and nt_mantissa str = nt_natural str
 
and nt_exponent str = caten nt_expon_token nt_integer str
 
and nt_floatA str = 
  let nt1 =
    caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent))) in 
  let nt1 = pack nt1 (fun (intpart, (p ,(mantis, exp))) -> match mantis,exp with
      |Some mantis , Some(_ ,exp) -> float_of_string (string_of_int intpart ^"."^string_of_int mantis ^"e"^string_of_int exp)
      |Some mantis , None -> float_of_string(string_of_int intpart ^ "." ^ string_of_int mantis)
      |None, Some (_,exp) -> float_of_string(string_of_int intpart ^ ".e" ^string_of_int exp)
      |None,None -> float_of_string(string_of_int intpart ^".")) in
  nt1 str
 
and nt_floatB str =
  let nt1 = caten (caten (char '.') nt_mantissa) (maybe nt_exponent) in
  let nt1 = pack nt1 (fun ((point,first),(second)) -> match second with
      | None -> float_of_string ("."^ (string_of_int first))
      | Some(_,num) -> match num with 
        | _ -> float_of_string ("."^ (string_of_int first) ^ "e" ^ (string_of_int num))) in
  nt1 str
and nt_floatC str =
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (base, (exp_token, exp))-> match exp_token with
      |_ -> float_of_string (string_of_int base ^ "e" ^string_of_int exp)) in
  nt1 str
     
     
and nt_float str  = 
  let nt1 = disj_list [nt_floatA;nt_floatB;nt_floatC] in
  let nt1 = caten nt_plus_or_minus nt1 in
  let nt1 = pack nt1 (fun x -> match x with
      |(Some '-',num)  -> ScmNumber (ScmReal (num *. -1.))
      |(Some '+',num) ->  ScmNumber (ScmReal num) 
      |(None, num) -> ScmNumber (ScmReal num)
      | _-> ScmNil) in nt1 str
                              
and nt_number str = disj_list[nt_float; nt_frac; nt_int] str
 
(* ------------------------------- *)

(* and nt_int str = raise X_not_yet_implemented *)
(* and nt_frac str = raise X_not_yet_implemented
and nt_integer_part str = raise X_not_yet_implemented
and nt_mantissa str = raise X_not_yet_implemented
and nt_exponent str = raise X_not_yet_implemented
and nt_float str = raise X_not_yet_implemented
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str *)

and nt_boolean = 
  let boolt = word_ci "#t" in 
  let boolf = word_ci "#f" in
  disj 
    (pack boolt (fun _ -> ScmBoolean(true))) 
    (pack boolf (fun _ -> ScmBoolean(false)))

and nt_char_simple str = (* raise X_not_yet_implemented *)
  let nt1 = diff nt_any nt_whitespace in
  (* let nt1 = not_followed_by nt1 nt1 in *)
  nt1 str;

and make_named_char name ch = pack (word_ci name) (fun n -> ch)

and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "nul" '\000');
               (make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
(* and nt_char_hex str = raise X_not_yet_implemented *)

(* and nt_char str = raise X_not_yet_implemented *)

(* ---------------------- *)
and char_prefix str = 
  let nt1 = char '#' in
  let nt2 = char '\\' in
  let nt1 = caten nt1 nt2 in
  nt1 str
and nt_char_hex str =
  let nt1 = char_ci 'x' in
  let nt2 = plus (disj_list [range '0' '9'; range_ci 'a' 'f']) in
  let nt2 = caten nt1 nt2 in
  let nt3 = pack nt2 (fun(x, num) -> char_of_int(int_of_string("0x" ^ list_to_string(num)))) in
  nt3 str;
and nt_char str = 
  let nt1 = disj_list [nt_char_hex;nt_char_named;nt_char_simple] in
  let nt2 = caten char_prefix nt1 in
  let nt3 = pack nt2 (fun(pre,ch)-> ScmChar ch) in
  nt3 str;
(* ----------------------------- *)

and nt_symbol_char str = 
  disj_list [range '0' '9'; range 'a' 'z'; range 'A' 'Z'; char '!'; char '$'; char '^'; char '*'; char '-'; char '_'; char '='; char '+'; char '<'; char '>'; char '?'; char '/'; char ':'; ] str

and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

(* and nt_string str = raise X_not_yet_implemented *)

(* ------------------------------- *)
and nt_digit_0_9 str =
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 (let delta = int_of_char '0' in
                      fun ch -> (int_of_char ch) - delta) in
  nt1 str
     
and nt_digit_a_f str =
  let nt1 = range_ci 'a' 'f' in
  let nt1 = pack nt1 Char.lowercase_ascii in
  let nt1 = pack nt1 (let delta = (int_of_char 'a') - 10 in
                      fun ch -> (int_of_char ch) - delta) in
  nt1 str
 
 
and nt_digit_0_f str =
  let nt1 = disj nt_digit_0_9 nt_digit_a_f in
  nt1 str
 
and nt_hex_nat str =
  let nt1 = plus nt_digit_0_f in
  let nt1 = pack nt1
      (fun digits ->
         List.fold_left
           (fun num digit ->
              16 * num + digit)
           0
           digits) in
  nt1 str
     
and nt_string_literal_char str =
  let nt1 = diff nt_any (disj_list [char '"';char '\\';char '~']) in
  nt1 str
 
 
and nt_string_meta_char str =
  disj_list [pack ( word "\\\\") (fun _ -> '\\');
             pack (word "\\r") (fun _ -> '\r');
             pack ( word "\\t") (fun _ -> '\t');
             pack (word "\\\"") (fun _ -> '\"');
             pack (word "\\n") (fun _ -> '\n');
             pack (word "\\f") (fun _ -> '\012');
             pack (word "~~") (fun _ -> '~')] str
 
and nt_string_char_hex str =
  let nt1 = caten (word "\\x") (caten nt_hex_nat (char ';')) in
  let nt1 = pack nt1 (fun (_, (n, _)) -> n) in
  let nt1 = only_if nt1 (fun n -> n < 256) in
  let nt1 = pack nt1 char_of_int in
  nt1 str
     
and nt_string_static_part str =
  let nt1 = disj_list [nt_string_literal_char;
                       nt_string_meta_char;
                       nt_string_char_hex] in
  let nt1 = pack (plus nt1) list_to_string in
  let nt1 = pack nt1 (fun str -> Static str) in
  nt1 str
                                                                 
and nt_string_dynamic_part str = 
  let nt1 = caten (word "~{") nt_sexpr in
  let nt1 = caten nt1 (char '}') in
  let nt1 = pack nt1 (fun ((_, sexpr), _) -> sexpr) in
  let nt1 = pack nt1 (fun sexpr ->
      ScmPair (ScmSymbol "format",
               ScmPair(ScmString "~a" ,
                       ScmPair (sexpr, ScmNil)))) in
  let nt1 = pack nt1 (fun sexpr -> Dynamic sexpr) in
  nt1 str
      
and nt_string str =
  let nt1 = char '"' in
  let nt2 = star (disj nt_string_static_part nt_string_dynamic_part) in
  let nt1 = caten nt1 (caten nt2 nt1) in
  let nt1 = pack nt1 (fun (_, (parts, _)) -> parts) in
  let nt1 = pack nt1 (function
      | [] -> ScmString ""
      | [Static str] -> ScmString str
      | [Dynamic sexpr] -> sexpr
      | parts ->
          let rest =
            (List.fold_right
               (fun car cdr ->
                  ScmPair((match car with
                      | Static str -> ScmString str
                      | Dynamic sexpr -> sexpr),
                          cdr))
               parts
               ScmNil) in
          ScmPair(ScmSymbol "string-append", rest)) in
  nt1 str
(* ------------------------------- *)

and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and pair_ctor lst = 
  match lst with
  | [] -> ScmNil
  | hd :: tl -> ScmPair(hd, pair_ctor tl)

and nt_proper_list str = 
  let nt1 = caten (caten (unitify (char '(')) (star nt_sexpr)) (unitify (char ')')) in
  let nt1 = pack nt1 (fun (( _ , sexprs_lst), _ ) -> pair_ctor sexprs_lst) in
  nt1 str

and nt_improper_list str = 
  let nt1 = caten (caten (caten (caten (char '(') (plus nt_sexpr)) (char '.')) nt_sexpr) (char ')') in
  let nt1 = pack nt1 (fun (((( _ , sexpr1), _ ), sexpr2), _ ) -> 
      List.fold_right (fun e1 e2 -> ScmPair(e1, e2)) sexpr1 sexpr2) in
  nt1 str

and nt_list str = 
  let nt1 = disj_list[nt_proper_list;nt_improper_list] in
  nt1 str

and nt_quote str = 
  let nt1 = caten (word "'") nt_sexpr in
  nt1 str

and nt_quasi_quote str = 
  let nt1 = caten (word "`") nt_sexpr in
  nt1 str
     
and nt_unquote str = 
  let nt1 = caten (word ",") nt_sexpr in
  nt1 str
 
and nt_unquote_and_splice str = 
  let nt1 = caten (word ",@") nt_sexpr in
  nt1 str

and nt_quoted_forms str = 
  let form qf sexp = ScmPair (ScmSymbol(qf) ,ScmPair (sexp, ScmNil)) in
  let nt1 = pack 
      (disj_list [nt_quote; 
                  nt_quasi_quote;
                  nt_unquote;
                  nt_unquote_and_splice]) 
      (fun (quote_type, sexp) -> match quote_type with
         |['\''] -> form "quote" sexp
         |['`'] -> form "quasiquote" sexp
         |[','] -> form "unquote" sexp
         |[',';'@'] -> form "unquote-splicing" sexp
         | _ -> ScmNil) in
  nt1 str


and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
