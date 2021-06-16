type token =
  | IDENT of (string)
  | NUM of (int)
  | AST
  | PLUS
  | MINUS
  | MOD
  | SLASH
  | EQ
  | NEQA
  | NEQB
  | LT
  | LE
  | GT
  | GE
  | TRUE
  | FALSE
  | LPAREN
  | RPAREN
  | COMMA
  | COLON
  | ATMARK
  | DOLLAR
  | SHARP
  | LSQPAREN
  | RSQPAREN
  | LCBRACKET
  | RCBRACKET
  | EOF

open Parsing;;
let _ = parse_error;;
# 4 "interval_parser.mly"
open Slsyntax
# 36 "interval_parser.ml"
let yytransl_const = [|
  259 (* AST *);
  260 (* PLUS *);
  261 (* MINUS *);
  262 (* MOD *);
  263 (* SLASH *);
  264 (* EQ *);
  265 (* NEQA *);
  266 (* NEQB *);
  267 (* LT *);
  268 (* LE *);
  269 (* GT *);
  270 (* GE *);
  271 (* TRUE *);
  272 (* FALSE *);
  273 (* LPAREN *);
  274 (* RPAREN *);
  275 (* COMMA *);
  276 (* COLON *);
  277 (* ATMARK *);
  278 (* DOLLAR *);
  279 (* SHARP *);
  280 (* LSQPAREN *);
  281 (* RSQPAREN *);
  282 (* LCBRACKET *);
  283 (* RCBRACKET *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* IDENT *);
  258 (* NUM *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\005\000\006\000\006\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\007\000\007\000\007\000\007\000\008\000\
\009\000\009\000\004\000\000\000"

let yylen = "\002\000\
\002\000\001\000\003\000\003\000\001\000\002\000\003\000\003\000\
\004\000\002\000\001\000\001\000\003\000\003\000\003\000\003\000\
\003\000\003\000\001\000\001\000\003\000\003\000\001\000\005\000\
\001\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\028\000\000\000\000\000\025\000\000\000\
\001\000\019\000\000\000\012\000\000\000\000\000\000\000\000\000\
\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\026\000\019\000\000\000\000\000\
\000\000\005\000\006\000\000\000\018\000\000\000\000\000\000\000\
\000\000\015\000\017\000\000\000\000\000\000\000\009\000\000\000\
\007\000\024\000\022\000\000\000"

let yydgoto = "\002\000\
\004\000\000\000\015\000\005\000\035\000\020\000\033\000\007\000\
\008\000"

let yysindex = "\008\000\
\074\255\000\000\030\255\000\000\070\000\002\255\000\000\046\255\
\000\000\000\000\003\255\000\000\002\255\098\255\055\255\030\255\
\000\000\006\255\099\255\080\255\072\255\081\255\002\255\002\255\
\002\255\002\255\002\255\002\255\000\000\000\000\006\255\082\255\
\025\255\000\000\000\000\099\255\000\000\080\255\087\255\015\255\
\015\255\000\000\000\000\077\255\072\255\048\255\000\000\002\255\
\000\000\000\000\000\000\082\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\027\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\033\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\054\255\
\000\000\000\000\000\000\000\000\000\000\050\255\254\254\023\255\
\045\255\000\000\000\000\000\000\084\255\000\000\000\000\000\000\
\000\000\000\000\000\000\078\255"

let yygindex = "\000\000\
\000\000\000\000\243\255\000\000\068\000\083\000\075\000\091\000\
\000\000"

let yytablesize = 107
let yytable = "\021\000\
\016\000\010\000\011\000\012\000\032\000\030\000\011\000\012\000\
\001\000\039\000\040\000\041\000\042\000\043\000\044\000\016\000\
\016\000\045\000\013\000\018\000\026\000\027\000\031\000\019\000\
\014\000\013\000\013\000\013\000\014\000\011\000\011\000\011\000\
\011\000\011\000\052\000\010\000\010\000\010\000\010\000\010\000\
\013\000\013\000\047\000\048\000\011\000\011\000\006\000\014\000\
\014\000\014\000\010\000\010\000\008\000\008\000\008\000\008\000\
\008\000\023\000\024\000\025\000\026\000\027\000\014\000\014\000\
\016\000\051\000\048\000\008\000\008\000\009\000\017\000\020\000\
\020\000\028\000\023\000\024\000\025\000\026\000\027\000\023\000\
\024\000\025\000\026\000\027\000\023\000\024\000\025\000\026\000\
\027\000\037\000\024\000\025\000\026\000\027\000\050\000\021\000\
\021\000\003\000\022\000\034\000\036\000\019\000\020\000\049\000\
\038\000\046\000\029\000"

let yycheck = "\013\000\
\003\001\000\001\001\001\002\001\018\000\000\001\001\001\002\001\
\001\000\023\000\024\000\025\000\026\000\027\000\028\000\018\001\
\019\001\031\000\017\001\017\001\006\001\007\001\017\001\021\001\
\023\001\003\001\004\001\005\001\023\001\003\001\004\001\005\001\
\006\001\007\001\048\000\003\001\004\001\005\001\006\001\007\001\
\018\001\019\001\018\001\019\001\018\001\019\001\017\001\003\001\
\004\001\005\001\018\001\019\001\003\001\004\001\005\001\006\001\
\007\001\003\001\004\001\005\001\006\001\007\001\018\001\019\001\
\019\001\018\001\019\001\018\001\019\001\000\000\025\001\018\001\
\019\001\019\001\003\001\004\001\005\001\006\001\007\001\003\001\
\004\001\005\001\006\001\007\001\003\001\004\001\005\001\006\001\
\007\001\018\001\004\001\005\001\006\001\007\001\018\001\018\001\
\019\001\024\001\001\001\001\001\021\001\021\001\019\001\036\000\
\022\000\031\000\016\000"

let yynames_const = "\
  AST\000\
  PLUS\000\
  MINUS\000\
  MOD\000\
  SLASH\000\
  EQ\000\
  NEQA\000\
  NEQB\000\
  LT\000\
  LE\000\
  GT\000\
  GE\000\
  TRUE\000\
  FALSE\000\
  LPAREN\000\
  RPAREN\000\
  COMMA\000\
  COLON\000\
  ATMARK\000\
  DOLLAR\000\
  SHARP\000\
  LSQPAREN\000\
  RSQPAREN\000\
  LCBRACKET\000\
  RCBRACKET\000\
  EOF\000\
  "

let yynames_block = "\
  IDENT\000\
  NUM\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'segment) in
    Obj.repr(
# 61 "interval_parser.mly"
        ( _1 )
# 192 "interval_parser.ml"
               : Slsyntax.Segments.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 66 "interval_parser.mly"
        ( [_1] )
# 199 "interval_parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 68 "interval_parser.mly"
        ( _1 @ [_3] )
# 207 "interval_parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string list) in
    Obj.repr(
# 70 "interval_parser.mly"
     ( _2 )
# 214 "interval_parser.ml"
               : string list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 76 "interval_parser.mly"
      (
        match _1 with
        | "PTR" | "ptr" -> T.PTR
        | "EXQ" | "exq" -> T.EXQ
        | "PARAM" | "param" -> T.PARAM
        | "PTRPTR" | "ptrptr" -> T.PTRPTR
        | "GLOBAL" | "global" -> T.GLOBAL
        | "HAT" | "hat" -> T.HAT
        | "BAR" | "bar" -> T.BAR
        | "EXTERN" | "extern" -> T.EXTERN
        | "TILDE" | "tilde" -> T.TILDE
        | "CHECK" | "check" -> T.CHECK
        | "DOT" | "dot" -> T.DOT
        | "NESTED" | "nested" -> T.NESTED
        | "QUESTION" | "question" -> T.QUESTION
        | "DOTDOT" | "dotdot" -> T.DOTDOT
        | "AQUTE" | "acute" -> T.ACUTE
        | "INDIRECT" | "indirect" -> T.INDIRECT
        | "PROTO" | "proto" -> T.PROTO
        | "ARRAY" | "array" -> T.ARRAY [1] 
        | _ -> T.STRUCT _1
      )
# 242 "interval_parser.ml"
               : 'var_attriv_one))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_attriv_one) in
    Obj.repr(
# 102 "interval_parser.mly"
      ( [_2] )
# 249 "interval_parser.ml"
               : 'var_attriv))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var_attriv) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'var_attriv_one) in
    Obj.repr(
# 104 "interval_parser.mly"
      ( _1 @ [_3] )
# 257 "interval_parser.ml"
               : 'var_attriv))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'var_attriv) in
    Obj.repr(
# 109 "interval_parser.mly"
        ( SHterm.Var ("#"^_2,_3) )
# 265 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term_seq) in
    Obj.repr(
# 111 "interval_parser.mly"
        ( SHterm.Fcall (_1,_3) )
# 273 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_attriv) in
    Obj.repr(
# 113 "interval_parser.mly"
        ( SHterm.Var (_1,_2) )
# 281 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 115 "interval_parser.mly"
        ( SHterm.Var (_1,[]) )
# 288 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 117 "interval_parser.mly"
        ( SHterm.Int _1 )
# 295 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : SHterm.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 119 "interval_parser.mly"
        (
          match _1,_3 with
          | SHterm.Add tt1,SHterm.Add tt2 -> SHterm.Add (tt1 @ tt2)
          | SHterm.Add tt1,_ -> SHterm.Add (tt1 @ [_3])
          | _,SHterm.Add tt2 -> SHterm.Add ([_1] @ tt2)
          | _,_ -> SHterm.Add [_1;_3]
        )
# 309 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : SHterm.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 127 "interval_parser.mly"
        ( SHterm.Sub [_1;_3] )
# 317 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : SHterm.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 129 "interval_parser.mly"
        ( SHterm.Mod (_1,_3) )
# 325 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : SHterm.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 131 "interval_parser.mly"
        ( SHterm.Mul (_1,_3) )
# 333 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : SHterm.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 133 "interval_parser.mly"
        ( SHterm.Div (_1,_3) )
# 341 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : SHterm.t) in
    Obj.repr(
# 135 "interval_parser.mly"
        ( _2 )
# 348 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    Obj.repr(
# 137 "interval_parser.mly"
        (
          let message =
            Printf.sprintf
              "parse error at line %d:%d-%d"
              ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
		      (Parsing.symbol_start ())
		      (Parsing.symbol_end ())
	      in
	      failwith message
        )
# 363 "interval_parser.ml"
               : SHterm.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 151 "interval_parser.mly"
        ( [_1] )
# 370 "interval_parser.ml"
               : 'term_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_seq) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : SHterm.t) in
    Obj.repr(
# 154 "interval_parser.mly"
        ( _1 @ [_3] )
# 378 "interval_parser.ml"
               : 'term_seq))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term_seq) in
    Obj.repr(
# 157 "interval_parser.mly"
     ( _2 )
# 385 "interval_parser.ml"
               : 'term_seq))
; (fun __caml_parser_env ->
    Obj.repr(
# 160 "interval_parser.mly"
        (
          let message =
            Printf.sprintf
              "parse error (term_seq) near characters %d-%d"
              (Parsing.symbol_start ())
	          (Parsing.symbol_end ())
	      in
	      failwith message
        )
# 399 "interval_parser.ml"
               : 'term_seq))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : SHterm.t) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : SHterm.t) in
    Obj.repr(
# 172 "interval_parser.mly"
        ( (_2,_4) )
# 407 "interval_parser.ml"
               : 'interval))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'interval) in
    Obj.repr(
# 176 "interval_parser.mly"
        ( [_1] )
# 414 "interval_parser.ml"
               : 'interval_seq))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'interval_seq) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'interval) in
    Obj.repr(
# 178 "interval_parser.mly"
        ( _1 @ [_3] )
# 422 "interval_parser.ml"
               : 'interval_seq))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval_seq) in
    Obj.repr(
# 182 "interval_parser.mly"
        ( _2 )
# 429 "interval_parser.ml"
               : 'segment))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Slsyntax.Segments.t)
