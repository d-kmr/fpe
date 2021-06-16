(* Lexer for biabd 2019/05/11 *)
(* Modified 2019/08/05 for biabduction extention *)

{
  open Slsyntax_parser_entl
}

let space = [' ' '\t' '\n' '\r']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z']
let idhead = alpha | ['$' '#' '_']
let alnum = digit | alpha | ['_' '\'' '%' '#']
let comment = "//"

                
rule token = parse
  | "->"      { PTO }            
  | '<'       { LT }
  | "<="      { LE }
  | '>'       { GT }  
  | ">="      { GE }  
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '%'       { PERCENT }
  | '/'       { SLASH }
  | '*'       { AST }
  | "=="      { EQ }      
  | '='       { EQ }
  | "!="      { NEQ }  
  | "=/"      { NEQ }
  | "<>"      { NEQ }
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
  | "#"       { HASH }
  
  | "Ex"      { EX }
  | "All"     { ALL }
  | "Arr"     { ARR }
  | "Array"   { ARR }
  | "Ls"      { LS }  
  | "Str"     { STR }
  | "Stringpart" { STRINGPART }
  | "Emp"     { EMP }
  | '&'       { AND }
  | "&&"      { AND }  
  | '|'       { OR }
  | "||"      { OR }  
  | "|-"      { VDASH }

  | "hat"     { HAT }
  | "bar"     { BAR }
  | "tilde"   { TILDE }
  | "dotdot"  { DOTDOT }  
  | "dot"     { DOT }
  | "HAT"     { HAT }
  | "BAR"     { BAR }
  | "GLOBAL"  { GLOBAL }  
  | "SIMPLE"  { SIMPLE }
  | "ARRAY"   { ARRAY }
  | "EXQ"     { EXQ }
  | "PTR"     { PTR }
  | "PTRPTR"  { PTRPTR }
  | "STRUCT"  { STRUCT }
  | "EXTERN"  { EXTERN }
  | "ACUTE"   { ACUTE }
  | "PARAM"   { PARAM }
  | "TILDE"   { TILDE }
  
  | idhead alnum*
    { IDENT (Lexing.lexeme lexbuf) }

  | digit*
    { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  
  | eof       { EOF }

  | space+    { token lexbuf }

  | comment [^ '\n' '\r']* eol { token lexbuf }

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

and comment = parse
  | eol     { token lexbuf }
  | eof     { EOF }            
  | _       { comment lexbuf }    
