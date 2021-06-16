// Parser for Biabd 2019/05/11

%{
open Slsyntax
%}

%token <string> IDENT  // x, y, P, ...
%token <int> NUM
            
%token AST      // '*'
%token PLUS     // '+'
%token MINUS	// '-'
%token PERCENT  // '%'
%token SLASH    // '/'
%token DOLLER   // '$'
            
%token EQ      // '=', "=="
%token NEQ     // "!=","<>","=/"
%token LT       // "<"
%token LE       // "<="            
%token GT       // ">" 
%token GE       // ">="
%token TRUE     // "True"
%token FALSE    // "False"
            
%token LPAREN   // '('
%token RPAREN   // ')'
%token LBRACKET // '['
%token RBRACKET // ']'            
%token COMMA    // ','
%token COLON    // ':'            
%token ATMARK   // '@'
%token DOLLAR   // '$'
%token HASH     // '#' 
            
%token EX       // "Ex"
%token ALL      // "All"
%token ARR  	// "Arr"
%token ARR  	// "Array"
%token STR  	// "Str"
%token STRINGPART 	// "Stringpart"
%token LS   	// "Ls"            
%token EMP  	// "Emp"
%token AND      // '&'
%token ANDAND   // "&&"
%token OR       // '|'
%token PTO      // "->"
%token VDASH    // "|-"

%token HAT      // "HAT"
%token GLOBAL   // "GLOBAL"            
%token BAR      // "BAR"
%token SIMPLE   // "SIMPLE"
%token EXQ      // "EXQ"
%token PTR      // "PTR"           
%token PARAM    // "PARAM"
%token PTRPTR   // "PTRPTR"
%token EXTERN   // "EXTERN"
%token TILDE    // "TILDE"
%token DOT      // "DOT"
%token DOTDOT   // "DOTDOT"
%token NESTED   // "NESTED"
%token QUESTION // "QUESTION"
%token ACUTE    // "ACUTE"
%token INDIRECT // "INDIRECT"
%token PROTO    // "PROTO"
%token ARRAY    // "ARRAY"
%token STRUCT   // "STRUCT"
%token TILDE    // "TILDE"

%token EOF 

// 結合力(優先度が低い順)
%nonassoc VDASH
%nonassoc EX
%nonassoc COLON
%left OR            
%left AND 
%left EQ NEQ
%left AST
%nonassoc PTO
%left PLUS MINUS
%left PERCENT SLASH
%left VAR NIL EMP LPAREN ATMARK DOLLAR

%start main
%type <Slsyntax.QFEntl.t> main
%type <string list> ident_seq
%type <SHterm.t> term
%type <SHspat.t> spat
%type <SHpure.t> pure
%type <QFSH.t> qfsh
%%

// 
main:
  | entl EOF
     { $1 }
;

ident_seq:
  | IDENT
      { [$1] }
  | LPAREN ident_seq RPAREN
	  { $2 }
;

attriv:
  | HAT
      { T.HAT }
  | PTR
      { T.PTR }
  | PARAM
      { T.PARAM }
  | PTRPTR
      { T.PTRPTR }
  | GLOBAL
      { T.GLOBAL }
  | EXQ
      { T.EXQ }
  | BAR
      { T.BAR }
  | EXTERN
      { T.EXTERN }
  | TILDE
      { T.TILDE }
  | DOT
      { T.DOT }
  | DOTDOT
      { T.DOTDOT }
  | NESTED
      { T.NESTED }
  | QUESTION
      { T.QUESTION }
  | ACUTE
      { T.ACUTE }
  | INDIRECT
      { T.INDIRECT }
  | PROTO
      { T.PROTO }
  | ARRAY LBRACKET NUM RBRACKET
      { T.ARRAY [$3] }
  | STRUCT IDENT
      { T.STRUCT $2 }
  | SIMPLE LPAREN NUM RPAREN
      { T.SIMPLE $3 }
;

vtype:
  | attriv
      { [$1] }
  | vtype COMMA attriv
      { $1 @ [$3] }
;  

vname:
  | IDENT
      { $1 }
  | IDENT EQ LPAREN IDENT COMMA IDENT RPAREN
      { $1 ^ "=(" ^ $4 ^ "," ^ $6 ^ ")" } 
;
  
term:
  | IDENT LPAREN term_seq RPAREN
      { SHterm.Fcall ($1,$3) }
  | vname ATMARK HAT
      { SHterm.Var ($1,[T.HAT]) }
  | vname ATMARK BAR
      { SHterm.Var ($1,[T.BAR]) }
  | vname ATMARK TILDE
      { SHterm.Var ($1,[T.TILDE]) }
  | vname ATMARK DOT
      { SHterm.Var ($1,[T.DOT]) }
  | vname ATMARK DOTDOT
      { SHterm.Var ($1,[T.DOTDOT]) }
  | vname LT vtype GT
      { SHterm.Var ($1,$3) }
  | vname
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
  | term PLUS LPAREN MINUS term RPAREN
      { SHterm.Sub [$1;$5] }
  | term MINUS term
      { SHterm.Sub [$1;$3] }
  | term PERCENT term               // t % t
      { SHterm.Mod ($1,$3) }
  | term AST term
      { SHterm.Mul ($1,$3) }
  | term SLASH term
      { SHterm.Div ($1,$3) }
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
  | term NEQ term
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
  | pure AND pure_atom
      { P.And [$1;$3] }
  | pure OR pure_atom
      { P.Or [$1;$3] }
  | ALL ident_seq pure
      { P.All($2,$3) }
  | EX ident_seq pure
      { P.Ex($2,$3) }
;      

pure_last:
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
  | STR LPAREN term COMMA term RPAREN	// Str ( t,t )
     { S.Str($3,$5) }
  | STRINGPART LPAREN term COMMA term RPAREN	// Stringpart ( t,t )
     { S.Str($3,$5) }  
  | LS LPAREN term COMMA term RPAREN // Ls(t,t)
     { S.Ind("Ls",[$3;$5]) }
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
  | pure AND spat
      { ($1,$3) }
;
  
entl:
   | qfsh VDASH qfsh
	  { ($1,[$3]) }
;
