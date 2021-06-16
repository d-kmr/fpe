type token =
  | IDENT of (string)
  | NUM of (int)
  | FUNCTIONHEADER of (string)
  | LT
  | LE
  | GT
  | GE
  | PLUS
  | MINUS
  | MOD
  | SLASH
  | LSHIFT
  | RSHIFT
  | HAT
  | TILDE
  | AST
  | EQ
  | NEQA
  | NEQB
  | TRUE
  | FALSE
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COLON
  | COMMA
  | ATMARK
  | DOLLAR
  | SHARP
  | BAND
  | BOR
  | FUNCTIONNAME
  | INPUT
  | OUTPUT
  | EX
  | ALL
  | ARR
  | ARRAY
  | STR
  | STRINGPART
  | EMP
  | AND
  | ANDAND
  | BAR
  | BARBAR
  | PTO
  | VDASH
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Slsyntax.MIfile.t
