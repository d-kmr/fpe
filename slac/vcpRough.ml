open Ftools

(* 
   definition =
   FUNDEF of single_name * block * cabsloc * cabsloc
 | S_FUNDEF of formula * formula * definition * cabsloc (* ** formula*formula as specification *)
 | S_INDDEF of indclause list * cabsloc
 | DECDEF of init_name_group * cabsloc        (* global variable(s), or function prototype *)
 | TYPEDEF of name_group * cabsloc
 | ONLYTYPEDEF of specifier * cabsloc
 | GLOBASM of string * cabsloc
 | PRAGMA of expression * cabsloc
 | LINKAGE of string * cabsloc * definition list (* extern "C" { ... } *)
 (* toplevel form transformer, from the first definition to the *)
 (* second group of definitions *)
 | TRANSFORMER of definition * definition list * cabsloc
 (* expression transformer: source and destination *)
 | EXPRTRANSFORMER of expression * expression * cabsloc

*)

(* and name = string * decl_type * attribute list * cabsloc

(* A variable declarator ("name") with an initializer *)
and init_name = name * init_expression *)

let get_exp = function
	| Cabs.NOTHING -> "nothing"
  | Cabs.UNARY (unary_operator, expression) -> "unary"
  | Cabs.LABELADDR (str) -> "label"  (* GCC's && Label *)
  | Cabs.BINARY (binary_operator, expression1, expression2) -> "binary"
  | Cabs.QUESTION (expression1, expression2, expression3) -> "question"

   (* A CAST can actually be a constructor expression *)
  | Cabs.CAST ((specifier, decl_type), init_expression) -> "cast"

    (* There is a special form of CALL in which the function called is
       __builtin_va_arg and the second argument is sizeof(T). This 
       should be printed as just T *)
  | Cabs.CALL (expression, l_expression) -> "call"
  | Cabs.COMMA (l_expression) -> "comma"
  | Cabs.CONSTANT (constant) -> "constant"
  | Cabs.PAREN (expression) -> "paren"
  | Cabs.VARIABLE (str) -> str
  | Cabs.EXPR_SIZEOF (expression) -> "expr"
  | Cabs.TYPE_SIZEOF (specifier, decl_type) -> "sizeof"
  | Cabs.EXPR_ALIGNOF (expression) -> "e_alignof"
  | Cabs.TYPE_ALIGNOF (specifier, decl_type) -> "t_alignof"
  | Cabs.INDEX (expression1 , expression2) -> "index"
  | Cabs.MEMBEROF (expression, string) -> "memberof"
  | Cabs.MEMBEROFPTR (expression, str) -> "memberptr"
  | Cabs.GNU_BODY (block) -> "block"
  | Cabs.EXPR_PATTERN (string) -> "expr_pattern"     (* pattern variable, and name *)

let get_type_specifier = function
	| Cabs.Tvoid -> "void"                             (* Type specifier ISO 6.7.2 *)
  | Cabs.Tchar -> "char"
  | Cabs.Tbool -> "bool"
  | Cabs.Tshort -> "short"
  | Cabs.Tint -> "int"
  | Cabs.Tlong -> "long"
  | Cabs.Tint64 -> "longlong"
  | Cabs.Tfloat -> "float"
  | Cabs.Tdouble -> "double"
  | Cabs.Tsigned -> "signed"
  | Cabs.Tsizet -> "size_t"   (* used temporarily to translate offsetof() *)
  | Cabs.Tunsigned -> "unsigned"
  | Cabs.Tnamed ( str ) -> str
  | Cabs.Tstruct (str, o_l_field_group, l_attribute) -> Bytes.cat "struct " str
  | Cabs.Tunion (str, o_l_field_group, l_attribute) -> "union"
  | Cabs.Tenum (str, o_l_field_group, l_attribute) -> "enum"
  | Cabs.TtypeofE (expression) -> "ttypeofe"                     (* GCC __typeof__ *)
  | Cabs.TtypeofT (specifier, decl_type) -> "ttypeoft"       (* GCC __typeof__ *)

let trans_init_expression = function
	| Cabs.NO_INIT -> pw "no_init" 
  | Cabs.SINGLE_INIT (expression) -> pw "single_init"
  | Cabs.COMPOUND_INIT (l) -> p "LEN:"; pl (List.length l)  (* for mainly array declaration *)
(*		let f (initwhat , init_expression) = p "." in
		List.iter f l *)
	
(*
let trans_attribute (str, l_expression) = ()
	pw "<attr>"; pw str; pw "["; List.iter (fun e -> pw (get_exp e)) l_expression; pw "]"; pw "</attr>" *)
let trans_name_type (str, decl_type, l_attribute, _) =  
	let str = if str = "" then newvar () else str in
	match decl_type with 
	| Cabs.PTR _ -> p "*"; pw str
	| _ -> pw str


let rec trans_decl_type = function
 | Cabs.JUSTBASE -> p "."                              (* Prints the declared name *)
 | Cabs.PARENTYPE (l_attribute1, decl_type, l_attribute2) ->
	begin 
	pw "PAREN"; 
	trans_decl_type decl_type;
	end
                                          (* Prints "(attrs1 decl attrs2)".
                                           * attrs2 are attributes of the
                                           * declared identifier and it is as
                                           * if they appeared at the very end
                                           * of the declarator. attrs1 can
                                           * contain attributes for the
                                           * identifier or attributes for the
                                           * enclosing type.  *)
 | Cabs.ARRAY (decl_type, l_attribute, expression) -> pw "array"; trans_decl_type decl_type
                                          (* Prints "decl [ attrs exp ]".
                                           * decl is never a PTR. *)
 | Cabs.PTR (l_attribute, decl_type) -> p "*" ; trans_decl_type decl_type     (* Prints "* attrs decl" *)
 | Cabs.PROTO (decl_type, l_single_name, vbool) -> pw "("; iterS (fun (s,n) -> trans_name_type n) "," l_single_name; pn ")"
                                          (* Prints "decl (args[, ...])".
                                           * decl is never a PTR.*)

let get_name_type (str, decl_type, l_attribute, _) =  
	let str = if str = "" then newvar () else str in
	match decl_type with 
	| Cabs.PTR _ -> (str, true)
	| _ -> (str, false)


let rec get_decl_type = function
 | Cabs.JUSTBASE -> ([], [])                              (* Prints the declared name *)
 | Cabs.PARENTYPE (l_attribute1, decl_type, l_attribute2) -> get_decl_type decl_type
 | Cabs.ARRAY (decl_type, l_attribute, expression) -> get_decl_type decl_type
 | Cabs.PTR (l_attribute, decl_type) -> let (x, y) = get_decl_type decl_type in (["*"], y)     (* Prints "* attrs decl" *)
 | Cabs.PROTO (decl_type, l_single_name, vbool) -> 
	let (x, y) = get_decl_type decl_type in  
	let n = List.map (fun (_, name) -> get_name_type name) l_single_name in
	(x, n @ y)


(*	List.iter trans_attribute l_attribute; *)
(*
Istia Islam
8/1, Rojoni Bosh Lane 
Laila Bhaban, 4th floor
Armanitola, Dhaka-1100
*)

(*		
let trans_init_name (name, init_expression) =
	trans_name name;
	trans_init_expression init_expression
*)		

let trans_spec_elem = function
	| Cabs.SpecTypedef -> pw "AA"          
  | Cabs.SpecCV (cvspec) ->  ()          (* const/volatile *)
  | Cabs.SpecAttr (attribute) -> pw "AA"      (* __attribute__ *)
  | Cabs.SpecStorage (storage) -> () 
  | Cabs.SpecInline -> pw "AA"
  | Cabs.SpecType (typeSpecifier) -> pw (get_type_specifier typeSpecifier)
  | Cabs.SpecPattern (str) -> pw "AA"
			  
let trans_init_name_group (l_spec_elem, l_init_name) =
	if List.length l_init_name > 1 then pw "EXCEPTION" else
	let init_name = (List.hd l_init_name) in
	let ((name, dt, _, _), _) = init_name in (* NOTE: we don't care attribute (3rd argument in 1st) *)
	match dt with 
	| Cabs.JUSTBASE 
	| Cabs.PARENTYPE (_,_,_) -> ()
	| Cabs.PROTO (decl_type, l_single_name, bo ) -> ()  (* perhaps only those prototype of which return type is not pointer *)
(*		begin 
			(* List.iter trans_spec_elem l_spec_elem; *)
			pw name; 
			match decl_type with
			| Cabs.JUSTBASE -> ()
			| Cabs.PARENTYPE (_,decl_type,_) -> trans_decl_type decl_type
			| _ -> () (* NEVER CASE *)
		end;
		pw "(";
		iterS (fun (l_spec, name) -> let (n, t) = get_name_type name in (* List.iter trans_spec_elem l_spec; if t then pw "*";*) pw n ) "," l_single_name; 
		pn ");";  (** First Achievement *) *)
	| Cabs.PTR (l_attribute, decl_type) -> 
		begin
		List.iter trans_spec_elem l_spec_elem;
		pw "*"; pw name;
		match decl_type with
		| Cabs.PTR (l_attribute, decl_type1) -> trans_decl_type decl_type1
		| Cabs.PROTO (decl_type, l_single_name, bo ) ->  
			iterS (fun (l_spec, name) -> let (n, t) = get_name_type name in (* List.iter trans_spec_elem l_spec; if t then pw "*";*) pw n ) "," l_single_name
		| _ -> ()
		end;
		pn ""
	| _ -> ()
(*		begin
			List.iter trans_spec_elem l_spec_elem; 
			pw "|"; 
			if List.length l_init_name > 1 then pw "EXCEPTION";
			trans_init_name init_name;
			pi 4
		end *)
		
let t_u_op = function 
	| Cabs.MINUS  -> "<-ve>"
	| Cabs.PLUS -> "<+ve>"
	| Cabs.NOT -> "<not>" 
	| Cabs.BNOT -> "<bnot>" 
	| Cabs.MEMOF -> "<memof>"
	| Cabs.ADDROF -> "<addrof>"
  | Cabs.PREINCR -> "<preincr>"
	| Cabs.PREDECR -> "<predecr>" 
	| Cabs.POSINCR -> "<posincr>" (* CAUTION *)
	| Cabs.POSDECR -> "<posdecr>" (* CAUTION *)
		
let t_b_op = function
	| Cabs.ADD -> "<add>" 
	| Cabs.SUB -> "<sub>" 
	| Cabs.MUL -> "<mul>" 
	| Cabs.DIV -> "<div>" 
	| Cabs.MOD -> "<mod>"
  | Cabs.AND -> "<and>"
	| Cabs.OR -> "<or>"
  | Cabs.BAND -> "<band>" 
	| Cabs.BOR -> "<bor>" 
	| Cabs.XOR -> "<xor>" 
	| Cabs.SHL -> "<shl>"
	| Cabs.SHR -> "<shr>"
  | Cabs.EQ -> "<eq>" 
	| Cabs.NE -> "<ne>"
	| Cabs.LT -> "<lt>" 
	| Cabs.GT -> "<gt>"
	| Cabs.LE -> "<le>" 
	| Cabs.GE -> "<ge>"
  | Cabs.ASSIGN -> "<assign>"
  | Cabs.ADD_ASSIGN -> "<add_assign>"
	| Cabs.SUB_ASSIGN -> "<sub_assign>" 
	| Cabs.MUL_ASSIGN -> "<mul_assign>"
	| Cabs.DIV_ASSIGN -> "<div_assign>" 
	| Cabs.MOD_ASSIGN -> "<mod_assign>"
  | Cabs.BAND_ASSIGN -> "<band_assign>"
	| Cabs.BOR_ASSIGN -> "<bor_assign>"
	| Cabs.XOR_ASSIGN -> "<xor_assign>"
	| Cabs.SHL_ASSIGN -> "<shl_assign>"
	| Cabs.SHR_ASSIGN -> "<shr_assign>"

let rec trans_expression = function
	| Cabs.NOTHING -> ()
  | Cabs.UNARY (unary_operator, expression) -> p (t_u_op unary_operator); trans_expression expression
  | Cabs.LABELADDR (str) -> p str; pn ":"  (* GCC's && Label *)
  | Cabs.BINARY (binary_operator, expression1, expression2) -> trans_expression expression1; p (t_b_op binary_operator); trans_expression expression2
  | Cabs.QUESTION (expression1, expression2, expression3) -> pw "if ("; trans_expression expression1; pw " ){"; trans_expression expression2; pw "} else {"; trans_expression expression3; pn "}"
  | Cabs.CAST ((specifier, decl_type), init_expression) -> 
		begin
			match init_expression with
      | Cabs.NO_INIT -> ()
      | Cabs.SINGLE_INIT (expression) -> trans_expression expression
      | Cabs.COMPOUND_INIT _ -> pw "EXCEPTION"
		end
  | Cabs.CALL (expression, l_expression) -> pw "cALL"; trans_expression expression; iterS trans_expression "," l_expression
  | Cabs.COMMA (l_expression) -> pw "cOMMA"; iterS trans_expression "," l_expression 
  | Cabs.CONSTANT (constant) -> 
		begin
			match constant with
			| Cabs.CONST_INT ( str ) -> p "<int>"; p str   (* the textual representation *)
      | Cabs.CONST_FLOAT ( str ) -> p "<float>"; p str  (* the textual representaton *)
      | Cabs.CONST_CHAR (l_int64) -> p "<char>"; pi (List.length l_int64) 
      | Cabs.CONST_WCHAR (l_int64) -> () (* not used *)
      | Cabs.CONST_STRING ( str ) -> p "<str>"; p str 
      | Cabs.CONST_WSTRING (l_int64) -> () (* not used *)
		end
  | Cabs.PAREN (expression) -> p "("; trans_expression expression; p ")"
  | Cabs.VARIABLE ( str ) -> p "<var>"; p str 
  | Cabs.EXPR_SIZEOF (expression) -> p "<sizeof>("; trans_expression expression; p ")"
  | Cabs.TYPE_SIZEOF (specifier, decl_type) -> pw "<type_sizeof>"
  | Cabs.EXPR_ALIGNOF (expression) -> () (* not used *)
  | Cabs.TYPE_ALIGNOF (specifier, decl_type) -> () (* not used *)
  | Cabs.INDEX (expression1, expression2) -> pw "<index>("; trans_expression expression1; p ")("; trans_expression expression2; p ")"
  | Cabs.MEMBEROF (expression, str) -> pw "<memberof>("; trans_expression expression; p ")["; p str; p "]" 
  | Cabs.MEMBEROFPTR (expression, str) -> pw "<memberofptr>("; trans_expression expression; p ")["; p str; p "]"
  | Cabs.GNU_BODY (block) -> pw "<block>"
  | Cabs.EXPR_PATTERN (str) -> () (* not used *)     (* pattern variable, and name *)
		
let rec trans_block sts = iterS (trans_body) "\n" sts  

	and trans_body = function
		|	Cabs.NOP (_) -> pw "nop" 
    | Cabs.COMPUTATION (expression, _) -> pw "computation A(A"; trans_expression expression; pw "A)A" 
    | Cabs.BLOCK (block, _) -> pw "block"; pw "["; trans_block block.bstmts ; pw "]"
    | Cabs.SEQUENCE (statement1, statement2, _) -> ()
    | Cabs.IF (expression, statement1, statement2, _) -> pw "if"; pw "("; trans_expression expression; pw ")"; pw "("; trans_body statement1; pw ")"; pw "("; trans_body statement2; pw ")"
    | Cabs.WHILE (formula, expression, statement, _) -> pw "while"; pw "("; trans_expression expression; pw ")"; pw "("; trans_body statement; pw ")"
    | Cabs.DOWHILE (formula, expression, statement, _) -> pw "dowhile"; pw "("; trans_expression expression; pw ")"; pw "("; trans_body statement; pw ")"
    | Cabs.FOR (formula, for_clause, expression1, expression2, statement, _) -> pw "for"; pw "("; trans_expression expression1; pw ")"; pw "("; trans_expression expression2; pw ")"; pw "("; trans_body statement; pw ")"
    | Cabs.BREAK (_) -> pw "break"
    | Cabs.CONTINUE (_) -> pw "continue" 
    | Cabs.RETURN (expression, _) -> pw "return = "; trans_expression expression;
    | Cabs.SWITCH (expression, statement, _) -> pw "switch" ; trans_expression expression; pw "("; trans_body statement; pw ")"
    | Cabs.CASE (expression, statement, _) -> pw "case"; trans_expression expression; pw "("; trans_body statement; pw ")"
    | Cabs.CASERANGE (expression1, expression2, statement, _) -> ()
    | Cabs.DEFAULT (statement, _) -> pw "default"; pw "("; trans_body statement; pw ")"
    | Cabs.LABEL (str, statement, _) -> pw "label:"; pw str; pw "("; trans_body statement; pw ")"
    | Cabs.GOTO (str, _) -> pw "goto:"; pw str
    | Cabs.COMPGOTO (expression, _) -> ()
    | Cabs.DEFINITION (definition) -> pw "definition" (*definition or declaration of a variable or type*)
    
    | Cabs.ASM (l_attribute, l_string, o_asm_details, _) -> pw "asm"    
       (** MS SEH *)
    | Cabs.TRY_EXCEPT (block1, expression, block2, _) -> ()
    | Cabs.TRY_FINALLY (block1, block2, _) -> ()


		
let rec translate = function
	| Cabs.FUNDEF ((spec, (name, dt, _, _)), b, _, ln) -> pw "fun: "; pw name; trans_decl_type dt; trans_block b.bstmts ; pw " -"; pi (List.length b.bstmts); pn "**************"
	| Cabs.S_FUNDEF (_, _, def, _) -> translate def
	| Cabs.S_INDDEF (_, _) -> ()
	| Cabs.DECDEF (x, ln) -> () (*trans_init_name_group x (* ; pl ln.lineno; pw ln.filename; pi 4 *)*)
	| Cabs.TYPEDEF (_, ln) -> () (* pl ln.lineno; pi 5 *)
	| Cabs.ONLYTYPEDEF (_, ln) -> () (* pl ln.lineno; pi 6 *)
 	| _ -> ()
