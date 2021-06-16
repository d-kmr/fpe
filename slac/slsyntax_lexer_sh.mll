(* Lexer for biabd 2019/05/11 *)
(* Modified 2019/08/05 for biabduction extention *)

{
  open Slsyntax_parser_sh
}

let space = [' ' '\t' '\n' '\r']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let alnum = digit | alpha | '\'' | '?'
let comment = "//"
  
rule token = parse
  | '<'       { LT }
  | "<="      { LE }
  | '>'       { GT }  
  | ">="      { GE }  
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '%'       { MOD }
  | '/'       { SLASH }
  | '*'       { AST }
  | '='       { EQA }
  | "=="      { EQB }  
  | "!="      { NEQA }
  | "=/"      { NEQB }  
  | "<>"      { NEQC }
  | "True"    { TRUE }
  | "False"   { FALSE }  
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | ':'       { COLON }
  | ','       { COMMA }
  | '@'       { ATMARK }
  | "$"       { DOLLAR }
  | "#"       { SHARP }
  
  | "Ex"      { EX }
  | "All"     { ALL }
  | "Arr"     { ARR }
  | "Array"   { ARRAY }
  | "Ls"      { LS }  
  | "Str"     { STR }
  | "Stringpart" { STRINGPART }
  | "Emp"     { EMP }
  | '&'       { AND }
  | '|'       { OR }
  | "->"      { PTO }
  | "|-"      { VDASH }
  
  | alpha alnum*
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
