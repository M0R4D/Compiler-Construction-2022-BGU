[1mFile "./reader.ml", line 76, characters 0-3[0m:
76 | let nt_boolean = 
     [1;31m^^^[0m
[1;31mError[0m: Syntax error: 'end' expected
[1mFile "./reader.ml", line 32, characters 25-31[0m:
32 | module Reader : READER = struct
                              [1;31m^^^^^^[0m
  This 'struct' might be unmatched
[1mFile "./tag-parser.ml", line 4, characters 16-21[0m:
4 |   | ScmConst of sexpr
                    [1;31m^^^^^[0m
[1;31mError[0m: Unbound type constructor sexpr
Hint: Did you mean expr?
[1mFile "./semantic-analyser.ml", line 18, characters 17-22[0m:
18 |   | ScmConst' of sexpr
                      [1;31m^^^^^[0m
[1;31mError[0m: Unbound type constructor sexpr
Hint: Did you mean expr'?
[1mFile "./code-gen.ml", line 16, characters 24-29[0m:
16 |   val make_consts_tbl : expr' list -> (sexpr * (int * string)) list
                             [1;31m^^^^^[0m
[1;31mError[0m: Unbound type constructor expr'
