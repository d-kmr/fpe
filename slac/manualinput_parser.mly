// Parser for Biabd 2019/05/11

%{
open Slsyntax
%}

%token <string> IDENT  // x, y, P, ...
%token <int> NUM
%token <string> FUNCTIONHEADER
            
%token LT       // "<"
%token LE       // "<="            
%token GT       // ">"               
%token GE       // ">="
%token PLUS     // '+'
%token MINUS	// '-'
%token MOD      // '%'
%token SLASH    // '/'
%token LSHIFT   // "<<"
%token RSHIFT   // ">>"
%token HAT      // '^'
%token TILDE    // '~'
%token AST      // '*'
%token EQ       // '='
%token NEQA     // "<>"
%token NEQB     // "=/"
%token TRUE     // "True"
%token FALSE    // "False"
%token LPAREN   // '('
%token RPAREN   // ')'
%token LBRACKET // '['
%token RBRACKET // ']'            
%token COLON    // ':'            
%token COMMA    // ','
%token ATMARK   // '@'
%token DOLLAR   // '$'
%token SHARP    // '#'
%token BAND     // "band"
%token BOR      // "bor"            
%token FUNCTIONNAME
%token INPUT
%token OUTPUT
            
%token EX       // "Ex"
%token ALL      // "All"
%token ARR  	// "Arr"
%token ARRAY  	// "Array"
%token STR  	// "Str"
%token STRINGPART 	// "Stringpart"
%token EMP  	// "Emp"
%token AND      // '&'
%token ANDAND	// "&&"            
%token BAR      // '|'
%token BARBAR   // "||"            
%token PTO      // "->"
%token VDASH    // "|-"

%token EOF 

// 結合力(優先度が低い順)
%nonassoc VDASH
%nonassoc EX
%nonassoc COLON
%left AND OR
%left EQ NEQA NEQB LT LE GT GE
%nonassoc PTO
%left RSHIFT LSHIFT            
%left PLUS MINUS
%left MOD SLASH AST
%left VAR NIL EMP LPAREN ATMARK DOLLAR

%start main
%type <Slsyntax.MIfile.t> main
%type <string list> ident_seq
%type <SHterm.t> term
%type <SHspat.t> spat
%type <SHpure.t> pure
%type <QFSH.t> qfsh
%%

// 
main:
  | file EOF
     { $1 }
;

ident_seq:
  | IDENT
      { [$1] }
  | ident_seq COMMA IDENT
      { $1 @ [$3] }
  | LPAREN ident_seq RPAREN
	  { $2 }
;

var_attriv_one:
  | IDENT
      {
        match $1 with
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
        | _ -> T.STRUCT $1
      }
;
  
var_attriv:
  | ATMARK var_attriv_one
      { [$2] }
  | var_attriv ATMARK var_attriv_one
      { $1 @ [$3] }
;
  
term:
  | SHARP IDENT var_attriv
      { SHterm.Var ("#"^$2,$3) }
  | IDENT LPAREN term_seq RPAREN
      { SHterm.Fcall ($1,$3) }
  | IDENT var_attriv
      { SHterm.Var ($1,$2) }
  | IDENT
    { SHterm.Var ($1,[]) }
  | NUM
    { SHterm.Int $1 }
  | term PLUS term
      {
        match $1,$3 with
        | SHterm.Add tt1,SHterm.Add tt2 -> SHterm.Add (tt1 @ tt2)
        | SHterm.Add tt1,_ -> SHterm.Add (tt1 @ [$3])
        | _,SHterm.Add tt2 -> SHterm.Add ([$1] @ tt2)
        | _,_ -> SHterm.Add [$1;$3]
      }
  | term PLUS MINUS term
      { SHterm.Sub [$1;$4] }
  | term MINUS term
      { SHterm.Sub [$1;$3] }
  | term MOD term
      { SHterm.Mod ($1,$3) }
  | term AST term
      { SHterm.Mul ($1,$3) }
  | term SLASH term
      { SHterm.Div ($1,$3) }
  | term LSHIFT term
      { SHterm.Shl ($1,$3) }
  | term RSHIFT term
      { SHterm.Shr ($1,$3) }
  | term BAND term
      { SHterm.Band ($1,$3) }
  | term BOR term
      { SHterm.Bor ($1,$3) }
  | term HAT term
      { SHterm.Bxor ($1,$3) }
  | TILDE term
      { SHterm.Bnot $2 }
  | LPAREN term RPAREN
      { $2 }
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error at line %d:%d-%d"
          ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
		  (Parsing.symbol_start ())
		  (Parsing.symbol_end ())
	    in
	    failwith message
    }	  
;

term_seq:
  | term
      { [$1] }
	  
  | term_seq COMMA term
      { $1 @ [$3] }

  | LPAREN term_seq RPAREN
	  { $2 }
	  
  | error
    { 
      let message =
        Printf.sprintf 
          "parse error (term_seq) near characters %d-%d"
          (Parsing.symbol_start ())
	      (Parsing.symbol_end ())
	    in
	    failwith message
    }	  	  
;

fieldterm:
  | term
      { ("",$1) }
  | AST COLON term
      { ("*",$3) }
  | IDENT COLON term
      { ($1,$3) }
;

fieldterm_seq:
  | fieldterm
      { [$1] }
  | fieldterm COMMA fieldterm_seq
      { $1 :: $3 }
;
  
pure_atom:
  | TRUE
      { P.True }
  | FALSE
      { P.False }
  | term EQ term
      { P.Atom(P.Eq,[$1;$3]) }
  | term NEQA term
      { P.Atom(P.Neq,[$1;$3]) }
  | term NEQB term
      { P.Atom(P.Neq,[$1;$3]) }
  | term LT term
      { P.Atom(P.Lt,[$1;$3]) }
  | term LE term
      { P.Atom(P.Le,[$1;$3]) }
  | term GT term
      { P.Atom(P.Lt,[$3;$1]) }
  | term GE term
      { P.Atom(P.Le,[$3;$1]) }
  | LPAREN pure RPAREN
      { $2 }
;

pure:
  | pure_atom
      { $1 }
  | pure AND pure
      { P.And [$1;$3] }
  | pure BAR pure
      { P.Or [$1;$3] }
  | ALL ident_seq pure
      { P.All($2,$3) }
  | EX ident_seq pure
      { P.Ex($2,$3) }
;      

pure_and:
  | pure AND
      { $1 }
;
  
spat_atom:
  | term PTO LPAREN RPAREN	// t -> ()
     { S.Pto($1,[]) }    
  | term PTO LPAREN fieldterm_seq RPAREN	// t -> (f1:t1,f2:t2)
     { S.Pto($1,$4) }
  | ARR LPAREN term COMMA term RPAREN	// Arr ( t,t )
     { S.Arr($3,$5) }
  | ARRAY LPAREN term COMMA term RPAREN	// Array ( t,t )
     { S.Arr($3,$5) }  
  | STR LPAREN term COMMA term RPAREN	// Str ( t,t )
     { S.Str($3,$5) }
  | STRINGPART LPAREN term COMMA term RPAREN	// Stringpart ( t,t )
     { S.Str($3,$5) }  
;

spat:
  | EMP
      { [] }
  | spat_atom
      { [$1] }
  | spat_atom AST spat
      { $1 :: $3 }
;

qfsh:
  | spat
      { (P.True,$1) }
  | pure_and spat
      { ($1,$2) }
;

var_asgn:
  | IDENT EQ term
      { ($1,$3) }
;

var_asgn_seq:
  | var_asgn
      { [$1] }
  | var_asgn_seq COMMA var_asgn
      { $1 @ [$3] }
;

store:
  | LBRACKET RBRACKET
      { [] }
  | LBRACKET var_asgn_seq RBRACKET
      { $2 }
;
  
input:
  | LPAREN store COMMA pure COMMA qfsh RPAREN
      { ($2,$4,$6) }
;

return:    
  | LPAREN term COMMA store COMMA pure COMMA qfsh COMMA qfsh RPAREN
      { ($2,$4,$6,$8,$10) }
;
  
return_seq:
  | return
      { [$1] }
  | return COMMA return_seq
      { $1 :: $3 }
;

funcIO:
  | FUNCTIONHEADER INPUT COLON input OUTPUT COLON
	   {
         let (s1,d1,sh1) = $4 in
         {
           MIfunctionIO.rawfunc = $1;
           MIfunctionIO.func = [];           
           MIfunctionIO.s = s1;
           MIfunctionIO.d = d1;
           MIfunctionIO.sh = sh1;
           MIfunctionIO.ret = []
         }
       }    
   | FUNCTIONHEADER INPUT COLON input OUTPUT COLON return_seq
	   {
         let (s1,d1,sh1) = $4 in
         {
           MIfunctionIO.rawfunc = $1;
           MIfunctionIO.func = [];
           MIfunctionIO.s = s1;
           MIfunctionIO.d = d1;
           MIfunctionIO.sh = sh1;
           MIfunctionIO.ret = $7
         }
       }    
;

funcIO_seq:
  | funcIO
      { [$1] }
  | funcIO funcIO_seq
      { $1 :: $2 }
;

file:
  | funcIO_seq
      { $1 }
;
  
