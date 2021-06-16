open Ftools;;
module C = Cabs;;

let rec transform_block block =
  {
    C.blabels = block.C.blabels;
    C.battrs  = block.C.battrs;
    C.bstmts  = transform_stmt |>>| block.C.bstmts
  }

and transform_stmt stmt =
  match stmt with
    C.NOP _ -> stmt
  | C.COMPUTATION (exp, cl) ->
     C.COMPUTATION (transform_exp exp, cl)
  | C.BLOCK (blk, cl) ->
     C.BLOCK (transform_block blk, cl)
  | C.SEQUENCE (stmt1, stmt2, cl) ->
     C.SEQUENCE (transform_stmt stmt1, transform_stmt stmt2, cl)
  | C.IF (exp, stmt1, stmt2, cl) ->
     C.IF (exp, transform_stmt stmt1, transform_stmt stmt2, cl)
  | C.WHILE (fml, exp, stmt, cl) ->
     C.WHILE (fml, exp, transform_stmt stmt, cl)
  | C.DOWHILE (fml, exp, stmt, cl) ->
     C.DOWHILE (fml, exp, transform_stmt stmt, cl)
  | C.FOR (fml, for_clause, exp1, exp2, stmt, cl) ->
     C.FOR (fml, for_clause, exp1, exp2, transform_stmt stmt, cl)
  | C.BREAK _ ->
     stmt
  | C.CONTINUE _ ->
     stmt
  | C.RETURN _ ->
     stmt
  | C.SWITCH (exp, stmt, cl) ->
     C.SWITCH (exp, transform_stmt stmt, cl)
  | C.CASE (exp, stmt, cl) ->
     C.CASE (exp, transform_stmt stmt, cl)
  | C.CASERANGE (exp1, exp2, stmt, cl) ->
     C.CASERANGE (exp1, exp2, transform_stmt stmt, cl)
  | C.DEFAULT (stmt, cl) ->
     C.DEFAULT (transform_stmt stmt, cl)
  | C.LABEL (str, stmt, cl) ->
     C.LABEL (str, transform_stmt stmt, cl)
  | C.GOTO _ ->
     stmt
  | C.COMPGOTO _ ->
     stmt
  | C.DEFINITION def ->
     C.DEFINITION (transform_def def)
  | C.ASM _ ->
     stmt
  | C.TRY_EXCEPT (blk1, exp, blk2, cl) ->
     C.TRY_EXCEPT (transform_block blk1, exp, transform_block blk2, cl)
  | C.TRY_FINALLY (blk1, blk2, cl) ->
     C.TRY_FINALLY (transform_block blk1, transform_block blk2, cl)

and transform_def = function
  | C.DECDEF ((spec, l_init_name), cl) ->
     C.DECDEF ((spec, transform_init_name |>>| l_init_name), cl)
  | def -> def

and transform_init_name (name, init_exp) =
    (name, transform_init_exp init_exp)

and transform_init_exp = function
    C.NO_INIT as ni ->
     ni
  | C.SINGLE_INIT exp ->
     C.SINGLE_INIT (transform_exp exp)
  | C.COMPOUND_INIT (l_iw_ie) ->
     C.COMPOUND_INIT ((fun (iw, ie) -> (iw, transform_init_exp ie)) |>>| l_iw_ie)
  
and transform_exp exp =
  match exp with
    C.NOTHING -> exp
  | C.UNARY (op, exp) ->
     C.UNARY (op, transform_exp exp)
  | C.LABELADDR _ ->
     exp
  | C.BINARY (op, exp1, exp2) ->
     C.BINARY (op, transform_exp exp1, transform_exp exp2)
  | C.QUESTION (exp1, exp2, exp3) ->
     C.QUESTION (transform_exp exp1, transform_exp exp2, transform_exp exp3)
  | C.CAST (spec_dt, init_exp) ->
     C.CAST (spec_dt, transform_init_exp init_exp)
  | C.CALL (exp, l_exp) ->
     
     C.CALL (transform_exp exp, transform_exp |>>| l_exp)
  | C.COMMA (l_exp) ->
     C.COMMA (transform_exp |>>| l_exp)
  | C.CONSTANT _ ->
     exp
  | C.PAREN exp ->
     C.PAREN (transform_exp exp)
  | C.VARIABLE _ ->
     exp
  | C.EXPR_SIZEOF exp ->
     C.EXPR_SIZEOF (transform_exp exp)
  | C.TYPE_SIZEOF _ ->
     exp
  | C.EXPR_ALIGNOF exp ->
     C.EXPR_ALIGNOF (transform_exp exp)
  | C.TYPE_ALIGNOF _ ->
     exp
  | C.INDEX (exp1, exp2) ->
     C.INDEX (transform_exp exp1, transform_exp exp2)
  | C.MEMBEROF (exp, fld) ->
     C.MEMBEROF (transform_exp exp, fld)
  | C.MEMBEROFPTR (exp, fld) ->
     C.MEMBEROFPTR (transform_exp exp, fld)
  | C.GNU_BODY blk ->
     C.GNU_BODY (transform_block blk)
  | C.EXPR_PATTERN _ ->
     exp
;;

let rec transform_global = function
    C.FUNDEF (single_name, block, cl1, cl2) ->
    C.FUNDEF (single_name, transform_block block, cl1, cl2)
  | def -> def
;;


let transform_cabs cabs =
	transform_global |>>| cabs
	;;
