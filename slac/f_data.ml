module Locs = struct
  type t = string * int
end

module Op = struct
  type t = ADD | SUB | MUL | DIV | MOD | EQ | NE | LE | OR | AND | DUMMY | SHL | SHR | BOR | BAND | MAPSTO
end

module Var = struct
  type attr = PTR | STRUCT of string | EXQ | ARRAY | PARAM | PTRPTR
  type t = string * attr list
end

module Exp = struct
	type t =
           NOTHING
	| VAR of Var.t
	| CONST of int  
	| FLOAT of float
	| BINOP of t * Op.t * t
	| INDICES of t list
end

module Term = struct 
	type t = 
		| EXP of Exp.t 
		| NULL 
end

module BExp = struct
  type t =
    | UNIT of Term.t * Op.t * Term.t
		| OP of t * Op.t * t
		| BLOCK of Var.t * Term.t
		| NOTHING
end

module Field = struct
  type t = string
end
    
module Pointer = struct
  type t = Term.t * (Field.t * Term.t) list
end

module Predicate = struct
  type t = string * Term.t list
  (** A special predicate, ("Array", [start_index; length]), is taken as an array *)
end

module Formula = struct
  type t = (string list * BExp.t list * Pointer.t list * Predicate.t list) list
end

(** An entailment is of type Formula.t * Formula.t, but it doesn't have a separate module *)
