#use "pc.ml"
#use "reader.ml";;
#use "tag-parser.ml";;
#use "semantic-analyser.ml";;
#use "code-gen.ml";;

open PC;;
open Reader;;
open Tag_Parser;;
open Semantic_Analysis;;

(* let test1 = Semantic_Analysis.annotate_lexical_addresses(
  (ScmDef ((ScmVar ("test")), (ScmLambdaOpt (["x"], "y", ScmApplic ((ScmVar ("cons")), [ScmVar ("x");ScmLambdaSimple ([], (ScmSet ((ScmVar ("x")), (ScmVar ("y")))))])))))
) *)

let alpha = 1;;
test_string nt_sexpr "#\\A" 0;;

let test2 = annotate_lexical_addresses(
  tag_parse_expression(
    (test_string nt_sexpr "(integer->char #\\A )" 0).found
  )
)
let test3 = Code_Gen.make_consts_tbl [
  run_semantics(
  tag_parse_expression(
    (test_string nt_sexpr "#\\A" 0).found
  )
)]
let test3 = Code_Gen.make_consts_tbl [
  run_semantics(
  tag_parse_expression(
    (test_string nt_sexpr "#\\B" 0).found
  )
)]
let test3 = Code_Gen.make_consts_tbl [
  run_semantics(
  tag_parse_expression(
    (test_string nt_sexpr "#\\C" 0).found
  )
)]
(* let test4 = annotate_lexical_addresses(
  tag_parse_expression(
    (test_string nt_sexpr "(not (> frily rocket))" 0).found
  )
) *)