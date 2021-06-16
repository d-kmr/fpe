(* Lexer for manualinput 2019/05/11 *)

{
open Manualinput_parser
}

let space = [' ' '\t' '\n' '\r']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let alnum = digit | alpha | '\''
let comment = "//"
let functionname = "functionname"

rule token = parse
  | '<'       { LT }
  | "<="      { LE }
  | '>'       { GT }
  | ">="      { GE }
  | '+'       { PLUS }
  | '-'       { MINUS }  
  | '%'       { MOD }
  | '/'       { SLASH }
  | "<<"      { LSHIFT }
  | ">>"      { RSHIFT }
  | '^'       { HAT }
  | '~'       { TILDE }
  | '*'       { AST }
  | '='       { EQ }
  | "=/"      { NEQA }
  | "<>"      { NEQB }
  | "True"    { TRUE }
  | "False"   { FALSE }  
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LBRACKET }
  | ']'       { RBRACKET }  
  | ':'       { COLON }
  | ','       { COMMA }
  | '@'       { ATMARK }
  | "$"       { DOLLAR }
  | "#"       { SHARP }
  | "input"   { INPUT }
  | "output"  { OUTPUT }
  | "bor"     { BOR }
  | "band"    { BAND }  
  | "functionname" { FUNCTIONNAME }  
  | "Ex"      { EX }
  | "All"     { ALL }
  | "Arr"     { ARR }
  | "Array"   { ARRAY }
  | "Str"     { STR }
  | "Stringpart" { STRINGPART }
  | "Emp"     { EMP }
  | "&&"      { ANDAND }
  | '&'       { AND }
  | '|'       { BAR }
  | "||"      { BARBAR }  
  | "->"      { PTO }
  | "|-"      { VDASH }

  | alpha alnum*
    { IDENT (Lexing.lexeme lexbuf) }

  | digit*
    { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  
  | eof       { EOF }

  | space+    { token lexbuf }

  | comment [^ '\n' '\r']* eol { token lexbuf }

  | functionname space* ":" space*
    { block_funcheader lexbuf }
  
  | _
    {
      let message = Printf.sprintf
        "unknown token %s near characters %d-%d"
        (Lexing.lexeme lexbuf)
        (Lexing.lexeme_start lexbuf)
        (Lexing.lexeme_end lexbuf)
      in
      failwith message
    }

and block_funcheader = parse
  | [^ '\n' '\r']* 
      { FUNCTIONHEADER (Lexing.lexeme lexbuf) }
  
and comment =
  parse
| eol     { token lexbuf }
| eof     { EOF }
| _       { comment lexbuf }
