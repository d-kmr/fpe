(* Program Transformer from C into extended-C *)
(*------------------------------------------------
After this transformation
- no 'do-while' (replaced by while)
- no 'break' and 'continue'
- 'return' appears as 'if-return' only at the top-level
- with special labels "@labelname" (not usual goto-label)

Other supporting features
-- no assignment operators like +=,*= etc
-- (support) 'switch' 
-- (support) 'for' (replaced by while)
-- (later support) no ternary operator '?' (replaced by if-else)
-- (later) forwarding-'goto'?

Ad-hoc trick: 
- For extended label '@L', use LABEL("@L",dummystatement,dummycabsloc)
- For labeled statement '@L:stat', use LABEL("@L",stat,dummycabsloc)
- For labeled statement '@L:stat:exp' with annotation expression, 
  write LABEL("@L",SWITCH(exp,stat),dummycabsloc) 
- For statement stat:exp with annotation expression, 
  write LABEL("",SWITCH(exp,stat),dummycabsloc) 
- For expression 'exp' with label '@L' (written 'exp@L' in the note), 
  use CALL(VARIABLE("@L"),[exp]) of type expression, namely '(@L)(exp)'
--------------------------------------------------*)
open Tools;;
open Cprint;;
open CtransformOptions;;
   
module C = Cabs
;;
exception Out (* Jump for output *)
;;

(* Label Counter *)
let lc = ref 0;;
let lc_reset () = lc := 0;;
let lc_incl () = lc := !lc + 1;;
let genLabelName () = (* making a new label name of the extended language *)
  let lname = "@L" ^ (string_of_int !lc) in
  lc_incl();
  lname
;;

(* Variable Counter *)
let vc = ref 0;;
let vc_reset () = vc := 0;;
let vc_incl () = vc := !vc + 1;;
let genVarName () = (* making a new variable name *)
  let vname = "@v" ^ (string_of_int !vc) in
  vc_incl();
  vname
;;

(* loop-depth *)
let loop_depth = ref 0;; (* 0 : not inside a loop *)
let inclLoopDepth () = loop_depth := !loop_depth + 1;;
let declLoopDepth () = loop_depth := !loop_depth - 1;;

(*---------------------------*)
(* Some tools for cabs data  *)
(*---------------------------*)
let dmy_cabsloc = (* dummy cabsloc *)
  {
    C.lineno = -1;
    C.filename = "added by ctransform";
    C.byteno = -1;
    C.ident = -1
  }

let getloc s = 
  match s with
  | C.NOP loc -> loc
  | C.COMPUTATION (_,loc) -> loc
  | C.BLOCK (_,loc) -> loc
  | C.SEQUENCE (_,_,loc) -> loc
  | C.IF (_,_,_,loc) -> loc
  | C.WHILE (_,_,_,loc) -> loc
  | C.DOWHILE (_,_,_,loc) -> loc
  | C.FOR (_,_,_,_,_,loc) -> loc
  | C.BREAK loc -> loc
  | C.CONTINUE loc -> loc
  | C.RETURN (_,loc) -> loc
  | C.SWITCH (_,_,loc) -> loc
  | C.CASE (_,_,loc) -> loc
  | C.CASERANGE (_,_,_,loc) -> loc
  | C.DEFAULT (_,loc) -> loc
  | C.LABEL (_,_,loc) -> loc
  | C.GOTO (_,loc) -> loc
  | C.COMPGOTO (_,loc) -> loc
  | C.DEFINITION _ -> dmy_cabsloc
  | C.ASM(_,_,_,loc) -> loc
  | C.TRY_EXCEPT (_,_,_,loc) -> loc
  | C.TRY_FINALLY (_,_,loc) -> loc

let getloc_block blk =
  let ss = blk.C.bstmts in
  if ss = [] then dmy_cabsloc else getloc (List.hd ss)
                             
let dmy_fml : C.formula = (* dummy formula *)
  ([],[],true,[],[])

let ss2stmt ss =
  match ss with
  | [] -> C.NOP dmy_cabsloc
  | [s] -> s
  | _ ->
     let locL = List.map getloc ss in
     let block = { C.blabels = []; C.battrs = []; C.bstmts = ss } in
     C.BLOCK(block,List.hd locL)

                             
(* Shortcuts for expressions *)
let _Not e = C.UNARY(C.NOT,e)
let ( |&| ) e1 e2 = C.BINARY(C.AND,e1,e2)
let ( ||| ) e1 e2 = C.BINARY(C.OR,e1,e2)
let ( |=| ) e1 e2 = C.BINARY(C.EQ,e1,e2)
let ( |<>| ) e1 e2 = C.BINARY(C.NE,e1,e2)
let _Question e1 e2 e3 = C.QUESTION (e1,e2,e3)
let eVar v = C.VARIABLE v
let eNum n = C.CONSTANT (C.CONST_INT (string_of_int n))
let eZero = eNum 0
let eOne = eNum 1
let eTwo = eNum 2
let eTrue = C.BINARY(C.EQ,eZero,eZero)

          
(* Shortcuts for statements *)                       
let _Nop = C.NOP dmy_cabsloc;;
let _Break loc = C.BREAK loc
let _Continue loc = C.CONTINUE loc
let _If eCond sThen sElse loc = C.IF(eCond,sThen,sElse,loc)
let _IfThen eCond sThen loc = _If eCond sThen _Nop loc
let _IfSS eCond ssThen ssElse loc = _If eCond (ss2stmt ssThen) (ss2stmt ssElse) loc
let _IfThenSS eCond ssThen loc = _If eCond (ss2stmt ssThen) _Nop loc
let _Return eVal loc =
  let eVal' = if eVal = C.NOTHING then eZero else eVal in
  C.RETURN(eVal',loc)
let _IfBreak eCond loc = _If eCond (_Break dmy_cabsloc) _Nop loc
let _IfContinue eCond loc = _If eCond (_Continue loc) _Nop loc
let _IfReturn eCond eVal loc =
  let eVal' = if eCond = C.NOTHING then eZero else eVal in
  _If eCond (_Return eVal' loc) _Nop loc
let _Label name sBody loc = C.LABEL(name,sBody,loc)
let _Label0 name loc = _Label name _Nop loc
let _LabelSS name ssBody loc = _Label name (ss2stmt ssBody) loc
let _While eCond sBody loc = C.WHILE (dmy_fml,eCond,sBody,loc)
let _WhileSS eCond ssBody loc = _While eCond (ss2stmt ssBody) loc
let _DoWhile eCond sBody loc = C.DOWHILE (dmy_fml,eCond,sBody,loc)
let _DoWhileSS eCond ssBody loc = _DoWhile eCond (ss2stmt ssBody) loc
let _For fcls e1 e2 sBody loc = C.FOR (dmy_fml,fcls,e1,e2,sBody,loc)
let _ForSS fcls e1 e2 ssBody loc = _For fcls e1 e2 (ss2stmt ssBody) loc
let _Switch eCond sBody loc = C.SWITCH(eCond,sBody,loc)
let _SwitchSS eCond ssBody loc = _Switch eCond (ss2stmt ssBody) loc
let _Case e sBody loc = C.CASE(e,sBody,loc)
let _CaseSS e ss loc = _Case e (ss2stmt ss) loc
let _CaseRange e1 e2 sBody loc = C.CASERANGE(e1,e2,sBody,loc)
let _CaseRangeSS e1 e2 ss loc = _CaseRange e1 e2 (ss2stmt ss) loc
let _Default sBody loc = C.DEFAULT (sBody,loc)
let _DefaultSS ssBody loc = _Default (ss2stmt ssBody) loc
                      
(* assignment *)
let ( |:=| ) v (e,loc) = C.COMPUTATION(C.BINARY (C.ASSIGN, C.VARIABLE v,e),loc)
  
(* Variable Declaration *)  
let specInt = C.SpecType C.Tint;;
let specChar = C.SpecType C.Tchar;;
let _VarDecl0 spectype var init_exp loc =
  C.DEFINITION (C.DECDEF(([spectype],[((var, C.JUSTBASE, [],loc),init_exp)]),loc));;
let _VarDeclInit spectype var exp loc = _VarDecl0 spectype var (C.SINGLE_INIT exp) loc;;
let _VarDecl spectype var loc = _VarDecl0 spectype var C.NO_INIT loc;;
let bigAnd ee =
  List.fold_left
    (fun e1 -> fun e2 -> if e1 = eTrue then e2 else e1 |&| e2)
    eTrue
    ee
;;
                  
let destructIf stmt =
  match stmt with
  | C.IF(eCond,sThen,sElse,loc) -> (eCond,sThen,sElse,loc)
  | _ -> failwith "not IF"

let destructOneIf ss =
  match ss with
  | [stmt] -> destructIf stmt
  | _ -> failwith "not singleton-IF"

       
(* Making 'e@L' *)
let ( |@| ) e lname = C.CALL(C.VARIABLE lname,[e])
                    
(* Loop Control *)
type loopControl =
  | BREAK of C.cabsloc
  | RETURN of C.expression * C.cabsloc (* 'RETURN e' is 'return(e)' *)
  | CONTINUE of C.cabsloc 
  | IFBREAK of C.expression * C.cabsloc (* 'IFBREAK e1' is 'if (e1) break' *)
  | IFRETURN of C.expression * C.expression * C.cabsloc (* 'IFBREAK(e1,e2)' is 'if (e1) return(e2)' *)
  | IFCONTINUE of C.expression * C.cabsloc (* 'IFCONTINUE e' is 'if (e) continue' *)
  | NotLoopControl
  | EMPTY
;;
let rec checkLoopControl stmt =
  match stmt with
  | C.BREAK loc -> BREAK loc
  | C.RETURN (eVal,loc) -> RETURN (eVal,loc)
  | C.CONTINUE loc -> CONTINUE loc
  | C.IF(eCond,sThen,_,loc) -> 
     begin
       match checkLoopControl sThen with
       | BREAK _ -> IFBREAK (eCond,loc)
       | RETURN (eVal,_) -> IFRETURN(eCond,eVal,loc)
       | CONTINUE _ -> IFCONTINUE (eCond,loc)
       | _ -> NotLoopControl
     end
  | C.BLOCK(b,loc) -> 
     begin
       match b.C.bstmts with
       | [s] -> checkLoopControl s
       | _ -> NotLoopControl
     end
  | _ -> NotLoopControl
;;
let liftL f emp other ss =
  match ss with
  | [] -> emp
  | [s] -> f s
  | _ -> other
;;
let checkLoopControlL = liftL checkLoopControl EMPTY NotLoopControl
;;
let isLoopControl stmt =
  match checkLoopControl stmt with
  | NotLoopControl -> false
  | _ -> true
;;
let isContinue stmt =
  match checkLoopControl stmt with
  | CONTINUE _ -> true
  | _ -> false
;;
let isBreak stmt =
  match checkLoopControl stmt with
  | BREAK _ -> true
  | _ -> false
;;  
let isReturn stmt =
  match checkLoopControl stmt with
  | RETURN _ -> true
  | _ -> false
;;
let isIfContinue stmt =
  match checkLoopControl stmt with
  | IFCONTINUE _ -> true
  | _ -> false
;;  
let isLoopControlRaw stmt = isContinue stmt || isBreak stmt || isReturn stmt
;;
let isLoopControlL = liftL isLoopControl false false;;
let isContinueL = liftL isContinue false false;;
let isReturnL = liftL isReturn false false;;
let isBreakL = liftL isBreak false false;;
let isLoopControlRawL = liftL isLoopControlRaw false false;;  

let rec noBreakControlReturn stmt =
  match stmt with
  | C.SEQUENCE(s1,s2,_)
    | C.IF(_,s1,s2,_) -> noBreakControlReturn s1 && noBreakControlReturn s2
  | C.WHILE(_,_,s,_)
    | C.DOWHILE(_,_,s,_)
    | C.FOR(_,_,_,_,s,_)
    | C.SWITCH(_,s,_)
    | C.CASE(_,s,_)
    | C.CASERANGE(_,_,s,_)
    | C.DEFAULT(s,_)
    | C.LABEL(_,s,_)
    -> noBreakControlReturn s
  | C.NOP _
    | C.COMPUTATION(_,_)
    | C.GOTO(_,_)
    | C.COMPGOTO(_,_)
    | C.ASM(_,_,_,_)
    -> true
  | C.BREAK _ -> false
  | C.CONTINUE _ -> false
  | C.RETURN(_,_) -> false
  | C.BLOCK(b,_) -> noBreakControlReturnBlock b
  | C.TRY_EXCEPT(b1,_,b2,_)
    | C.TRY_FINALLY(b1,b2,_) ->
     (noBreakControlReturnBlock b1) && (noBreakControlReturnBlock b2)
  | C.DEFINITION def -> noBreakControlReturnDef def
                  
and noBreakControlReturnBlock b = List.for_all noBreakControlReturn b.C.bstmts 

and noBreakControlReturnDef def =
  match def with
  | C.FUNDEF(_,b,_,_) -> noBreakControlReturnBlock b
  | C.S_FUNDEF(_,_,d,_) -> noBreakControlReturnDef d
  | C.LINKAGE(_,_,dd) -> List.for_all noBreakControlReturnDef dd
  | C.TRANSFORMER(d,dd,_) -> List.for_all noBreakControlReturnDef (d::dd)
  | C.S_INDDEF(_,_)
    | C.DECDEF(_,_)
    | C.TYPEDEF(_,_)
    | C.ONLYTYPEDEF(_,_)
    | C.GLOBASM(_,_)
    | C.PRAGMA(_,_)
    | C.EXPRTRANSFORMER(_,_,_) -> true
;;

(*---------------
Variable renaming
- getting variables (vars_statement)
- renaming (rename_statement)
----------------*)
let rec vars_statement stmt =
  match stmt with
  | C.BLOCK (blk,_) -> vars_block blk
  | C.SEQUENCE (stmt1,stmt2,_) ->
     let vars1 = vars_statement stmt1 in
     let vars2 = vars_statement stmt2 in
     unionL [vars1; vars2]
  | C.IF (exp,stmt1,stmt2,_) ->
     let vars0 = vars_expression exp in
     let vars1 = vars_statement stmt1 in
     let vars2 = vars_statement stmt2 in
     unionL [vars0; vars1; vars2]
  | C.WHILE (_,exp,stmt1,_) ->
     let vars0 = vars_expression exp in
     let vars1 = vars_statement stmt1 in
     unionL [vars0; vars1]
  | C.DOWHILE (_,exp,stmt1,_) ->
     let vars0 = vars_expression exp in
     let vars1 = vars_statement stmt1 in
     unionL [vars0; vars1]
  | C.FOR (_,for_cls,exp0,exp1,stmt2,_) ->
     let vars = vars_for_clause for_cls in
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     let vars2 = vars_statement stmt2 in
     unionL [vars; vars0; vars1; vars2]
  | C.RETURN (exp,_)
    | C.COMPUTATION (exp,_) -> vars_expression exp
  | C.SWITCH (exp,stmt1,_)
    | C.CASE (exp,stmt1,_) ->
     let vars0 = vars_expression exp in
     let vars1 = vars_statement stmt1 in
     unionL [vars0; vars1]
  | C.CASERANGE (exp0,exp1,stmt2,_) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     let vars2 = vars_statement stmt2 in
     unionL [vars0; vars1; vars2]
  | C.DEFAULT (stmt1,_) -> vars_statement stmt1
  | C.LABEL (_,stmt1,_) -> vars_statement stmt1
  | C.COMPGOTO (exp,_) -> vars_expression exp
  | C.DEFINITION def -> vars_definition def
  | C.ASM _ -> []
  | C.TRY_EXCEPT (blk0,exp1,blk2,_) ->
     let vars0 = vars_block blk0 in
     let vars1 = vars_expression exp1 in
     let vars2 = vars_block blk2 in
     unionL [vars0; vars1; vars2]
  | C.TRY_FINALLY (blk0,blk1,_) ->
     let vars0 = vars_block blk0 in
     let vars1 = vars_block blk1 in
     unionL [vars0; vars1]
  | C.NOP _ 
    | C.BREAK _ 
    | C.CONTINUE _ 
    | C.GOTO (_,_) -> []
and vars_expression exp =
  match exp with
  | C.NOTHING -> []
  | C.UNARY (_,exp0) -> vars_expression exp0
  | C.LABELADDR _ -> []
  | C.BINARY (_,exp0,exp1) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     unionL [vars0; vars1]
  | C.QUESTION (exp0,exp1,exp2) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     let vars2 = vars_expression exp2 in     
     unionL [vars0; vars1; vars2]
  | C.CAST (_,initexp) -> vars_init_expression initexp
  | C.CALL (exp0,expL) ->
     let vars0 = vars_expression exp0 in
     let varsL = List.map vars_expression expL in
     unionL (vars0 :: varsL)
  | C.COMMA expL ->
     unionL (List.map vars_expression expL)
  | C.CONSTANT const -> vars_constant const
  | C.PAREN exp0 -> vars_expression exp0
  | C.VARIABLE v -> [v]
  | C.EXPR_SIZEOF exp0 -> vars_expression exp0
  | C.TYPE_SIZEOF _ -> []
  | C.EXPR_ALIGNOF exp0 -> vars_expression exp0
  | C.TYPE_ALIGNOF _ -> []
  | C.INDEX (exp0,exp1) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     unionL [vars0; vars1]
  | C.MEMBEROF (exp0,_) -> vars_expression exp0
  | C.MEMBEROFPTR (exp0,_) -> vars_expression exp0
  | C.GNU_BODY blk -> vars_block blk
  | C.EXPR_PATTERN str -> [str]
and vars_constant const = []
and vars_init_expression iexp =
  match iexp with
  | C.NO_INIT -> []
  | C.SINGLE_INIT exp0 -> vars_expression exp0
  | C.COMPOUND_INIT iwhat_iexpL ->
     let g (iwhat,iexp) = (vars_initwhat iwhat)@(vars_init_expression iexp) in
     unionL (List.map g iwhat_iexpL)
and vars_initwhat iwhat =
  match iwhat with
  | C.NEXT_INIT -> []
  | C.INFIELD_INIT _ -> []
  | C.ATINDEX_INIT (exp0,iwhat1) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_initwhat iwhat1 in
     unionL [vars0; vars1]
  | C.ATINDEXRANGE_INIT (exp0,exp1) -> 
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     unionL [vars0; vars1]
and vars_block blk = 
  let stmtL = blk.C.bstmts in
  unionL (List.map vars_statement stmtL)
and vars_for_clause forcls = 
  match forcls with
  | C.FC_EXP exp0 -> vars_expression exp0
  | C.FC_DECL def -> vars_definition def
and vars_definition def =
  match def with
  | C.FUNDEF (_,blk,_,_) -> vars_block blk
  | C.S_FUNDEF (_,_,def,_) -> vars_definition def
  | C.S_INDDEF (iclsL,_) ->
     unionL (List.map vars_indclause iclsL)
  | C.DECDEF _ -> []
  | C.TYPEDEF _ -> []
  | C.ONLYTYPEDEF _ -> []
  | C.GLOBASM _ -> []
  | C.PRAGMA _ -> []
  | C.LINKAGE _ -> []
  | C.TRANSFORMER (def,defL,_) ->
     unionL (List.map vars_definition (def::defL))
  | C.EXPRTRANSFORMER (exp0,exp1,_) ->
     let vars0 = vars_expression exp0 in
     let vars1 = vars_expression exp1 in
     unionL [vars0; vars1]
and vars_indclause icls = [] 
;;


module Renamer = struct

  type t =
    {
      mutable counter: int;
      (* renaming stack [ [(z,z_2)]; [(w,w_1);(v,v_0)] ] *)
      (* z,w,v are local var names. z is in the current scope *)
      (* z_2,w_1,v_0 are new local var names *)
      mutable renstack: ((bytes * bytes) list) list; 
    }

  let to_string ren =
    let counter' = string_of_int ren.counter in
    let f1 (s1,s2) = "(" ^ s1 ^ "," ^ s2 ^ ")" in
    let f2 ssL = "[" ^ (string_of_list f1 "," ssL) ^ "]" in
    let stack' = "[" ^ (string_of_list f2 "," ren.renstack) ^ "]" in
    "counter: " ^ counter' ^ "\n" ^
      "stack: " ^ stack'

  let println ren = print_endline (to_string ren) 
    
  let init () =
    {
      counter = 0;
      renstack = [[]];
    }
    
  (* perform renaming *)
  let rename ren x =
    let sub = List.flatten ren.renstack in
    try
      List.assoc x sub
    with
      Not_found -> x

  (* push local variable *)
  (* this is called when the renamer enters a block *)
  let push ren = 
    ren.renstack <- [] :: ren.renstack

  (* pop local variable *)
  (* this is called when the renamer leaves a block *)
  let pop ren =
    ren.renstack <- List.tl ren.renstack

  (* adding a new local variable *)
  (* the counter is incremented *)
  let addvar ren (v : bytes) =
    let v' = v ^ "_" ^ (string_of_int ren.counter) in
    ren.counter <- ren.counter + 1;
    ren.renstack <- ((v,v') :: List.hd ren.renstack) :: (List.tl ren.renstack)

    
end
;;


let rec rename_statement (ren: Renamer.t) stmt =
  match stmt with
  | C.NOP _ -> stmt
  | C.BREAK _ -> stmt
  | C.CONTINUE _ -> stmt
  | C.GOTO (_,_) -> stmt
  | C.ASM _ -> stmt
  | C.BLOCK (blk,loc) ->
     let blk' = rename_block ren blk in
     C.BLOCK(blk',loc)
  | C.SEQUENCE (stmt1,stmt2,loc) ->
     let stmt1' = rename_statement ren stmt1 in
     let stmt2' = rename_statement ren stmt2 in
     C.SEQUENCE (stmt1',stmt2',loc)
  | C.IF (exp,stmt1,stmt2,loc) ->
     let exp' = rename_expression ren exp in
     let stmt1' = rename_statement ren stmt1 in
     let stmt2' = rename_statement ren stmt2 in
     C.IF (exp',stmt1',stmt2',loc)
  | C.WHILE (fml,exp,stmt1,loc) ->
     let exp' = rename_expression ren exp in
     let stmt1' = rename_statement ren stmt1 in
     C.WHILE (fml,exp',stmt1',loc)
  | C.DOWHILE (fml,exp,stmt1,loc) ->
     let exp' = rename_expression ren exp in
     let stmt1' = rename_statement ren stmt1 in
     C.DOWHILE (fml,exp',stmt1',loc)
  | C.RETURN (exp,loc) ->
     let exp' = rename_expression ren exp in
     C.RETURN (exp',loc)
  | C.COMPUTATION (exp,loc) ->
     let exp' = rename_expression ren exp in
     C.COMPUTATION (exp',loc)
  | C.DEFAULT (stmt1,loc) ->
     let stmt1' = rename_statement ren stmt1 in
     C.DEFAULT (stmt1',loc)
  | C.LABEL (lbl,stmt1,loc) ->
     let stmt1' = rename_statement ren stmt1 in
     C.LABEL (lbl,stmt1',loc)
  | C.COMPGOTO (exp,loc) ->
     let exp' = rename_expression ren exp in
     C.COMPGOTO (exp',loc)
  | C.FOR (fml,for_cls,exp0,exp1,stmt2,loc) ->
     Renamer.push ren; (* do push *)     
     let for_cls' = rename_forcls ren for_cls in
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     let stmt2' = rename_statement ren stmt2 in
     Renamer.pop ren; (* do pop *)     
     C.FOR (fml,for_cls',exp0',exp1',stmt2',loc)
  | C.SWITCH (exp,stmt1,loc) ->
     let exp' = rename_expression ren exp in
     let stmt1' = rename_statement ren stmt1 in
     C.SWITCH (exp',stmt1',loc)
  | C.CASE (exp,stmt1,loc) ->
     let exp' = rename_expression ren exp in
     let stmt1' = rename_statement ren stmt1 in
     C.CASE (exp',stmt1',loc)
  | C.DEFINITION def ->     
     let def' = rename_definition ren def in
     C.DEFINITION def'
  | C.CASERANGE (exp0,exp1,stmt2,loc) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     let stmt2' = rename_statement ren stmt2 in
     C.CASERANGE (exp0',exp1',stmt2',loc)
  | C.TRY_EXCEPT (blk0,exp1,blk2,loc) ->
     let blk0' = rename_block ren blk0 in
     let exp1' = rename_expression ren exp1 in
     let blk2' = rename_block ren blk2 in
     C.TRY_EXCEPT (blk0',exp1',blk2',loc)
  | C.TRY_FINALLY (blk0,blk1,loc) ->
     let blk0' = rename_block ren blk0 in     
     let blk1' = rename_block ren blk1 in
     C.TRY_FINALLY (blk0',blk1',loc)
and rename_expression ren exp =
  match exp with
  | C.NOTHING -> exp
  | C.LABELADDR _ -> exp
  | C.CONSTANT _ -> exp
  | C.TYPE_SIZEOF _ -> exp
  | C.TYPE_ALIGNOF _ -> exp
  | C.EXPR_PATTERN str -> exp
  | C.UNARY (op,exp0) ->
     let exp0' = rename_expression ren exp0 in
     C.UNARY (op,exp0')
  | C.BINARY (binop,exp0,exp1) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     C.BINARY (binop,exp0',exp1')
  | C.QUESTION (exp0,exp1,exp2) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     let exp2' = rename_expression ren exp2 in
     C.QUESTION (exp0',exp1',exp2')
  | C.CAST ((spec,decl_type),initexp) ->
     let decl_type' = rename_decl_type ren decl_type in
     let initexp' = rename_init_expression ren initexp in
     C.CAST ((spec,decl_type'),initexp')
  | C.CALL (exp0,expL) ->
     let exp0' = rename_expression ren exp0 in
     let expL' = List.map (rename_expression ren) expL in
     C.CALL (exp0',expL')
  | C.COMMA expL ->
     let expL' = List.map (rename_expression ren) expL in
     C.COMMA expL'
  | C.PAREN exp0 ->
     let exp0' = rename_expression ren exp0 in
     C.PAREN exp0'
  | C.VARIABLE v ->
     let v' = Renamer.rename ren v in
     C.VARIABLE v'
  | C.EXPR_SIZEOF exp0 ->
     let exp0' = rename_expression ren exp0 in
     C.EXPR_SIZEOF exp0'
  | C.EXPR_ALIGNOF exp0 -> 
     let exp0' = rename_expression ren exp0 in
     C.EXPR_ALIGNOF exp0'
  | C.INDEX (exp0,exp1) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     C.INDEX (exp0',exp1')
  | C.MEMBEROF (exp0,str) -> 
     let exp0' = rename_expression ren exp0 in
     C.MEMBEROF (exp0',str)
  | C.MEMBEROFPTR (exp0,str) ->
     let exp0' = rename_expression ren exp0 in     
     C.MEMBEROFPTR (exp0',str)
  | C.GNU_BODY blk ->
     let blk' = rename_block ren blk in
     C.GNU_BODY blk'
and rename_init_expression ren initexp =
  match initexp with
  | C.NO_INIT -> initexp
  | C.SINGLE_INIT exp0 ->
     let exp0' = rename_expression ren exp0 in
     C.SINGLE_INIT exp0'
  | C.COMPOUND_INIT iwhat_iexpL ->
     let f (iwhat,iexp) =
       let iexp' = rename_init_expression ren iexp in
       let iwhat' = rename_initwhat ren iwhat in
       (iwhat',iexp')
     in
     let iwhat_iexpL' = List.map f iwhat_iexpL in
     C.COMPOUND_INIT iwhat_iexpL'
and rename_initwhat ren iwhat =
  match iwhat with
  | C.NEXT_INIT -> iwhat
  | C.INFIELD_INIT (str,iwhat0) ->
     let iwhat0' = rename_initwhat ren iwhat0 in
     C.INFIELD_INIT (str,iwhat0')
  | C.ATINDEX_INIT (exp0,iwhat0) ->
     let exp0' = rename_expression ren exp0 in
     let iwhat0' = rename_initwhat ren iwhat0 in
     C.ATINDEX_INIT (exp0',iwhat0')
  | C.ATINDEXRANGE_INIT (exp0,exp1) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     C.ATINDEXRANGE_INIT (exp0',exp1')
and rename_block ren blk =
     Renamer.push ren; (* do push *)     
     let blk' =
       {
         C.blabels = blk.C.blabels;
         C.battrs = blk.C.battrs;
         C.bstmts = List.map (rename_statement ren) blk.C.bstmts;
       }
     in
     Renamer.pop ren; (* do pop *)
     blk'
and rename_forcls ren for_cls =
  match for_cls with
  | C.FC_EXP exp ->
     let exp' = rename_expression ren exp in
     C.FC_EXP exp'
  | C.FC_DECL def ->
     let def' = rename_definition ren def in     
     C.FC_DECL def'
and rename_definition ren def =
  match def with
  | C.GLOBASM _ -> def
  | C.ONLYTYPEDEF _ -> def
  | C.TYPEDEF _ -> def
  | C.PRAGMA (exp,loc) ->
     let exp' = rename_expression ren exp in
     C.PRAGMA (exp',loc)
  | C.LINKAGE (str,loc,defL) ->
     let defL' = List.map (rename_definition ren) defL in
     C.LINKAGE (str,loc,defL')
  | C.S_FUNDEF (fml0,fml1,def0,loc) ->
     let def0' = rename_definition ren def0 in
     C.S_FUNDEF (fml0,fml1,def0',loc)
  | C.TRANSFORMER (def0,defL,loc) ->
     let def0' = rename_definition ren def0 in
     let defL' = List.map (rename_definition ren) defL in
     C.TRANSFORMER (def0',defL',loc)
  | C.FUNDEF (single_name,blk,loc0,loc1) -> 
     let single_name' = rename_single_name ren single_name in
     let blk' = rename_block ren blk in     
     C.FUNDEF (single_name',blk',loc0,loc1)
  | C.S_INDDEF (indclauseL,loc) ->
     let indclauseL' = List.map (rename_indclause ren) indclauseL in
     C.S_INDDEF (indclauseL',loc)
  | C.DECDEF (init_name_group,loc) ->
     let init_name_group' = rename_init_name_group ren init_name_group in
     C.DECDEF (init_name_group',loc)
  | C.EXPRTRANSFORMER (exp0,exp1,loc) -> 
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     C.EXPRTRANSFORMER (exp0',exp1',loc)
and rename_single_name ren single_name =
  single_name (* do nothing *)
and rename_indclause ren indclause =
  indclause (* do nothing *)
and rename_init_name_group ren init_name_group =
  let (tp, init_nameL) = init_name_group in
  let init_nameL' = List.map (rename_init_name ren) init_nameL in
  (tp, init_nameL')
and rename_init_name ren init_name =
  let (name,init_exp) = init_name in
  let name' = rename_name ren name in
  let init_exp' = rename_init_exp ren init_exp in
  (name',init_exp')
and rename_name ren name =
  let (v,decl_type,attrL,loc) = name in
  Renamer.addvar ren v;
  let v' = Renamer.rename ren v in
  let decl_type' = rename_decl_type ren decl_type in
  (v',decl_type',attrL,loc)
and rename_init_exp ren init_exp =
  match init_exp with
  | C.NO_INIT -> init_exp
  | C.SINGLE_INIT exp0 ->
     let exp0' = rename_expression ren exp0 in
     C.SINGLE_INIT exp0'
  | C.COMPOUND_INIT iwhat_iexpL ->
     let f (iwhat,iexp) =
       let iwhat' = rename_init_what ren iwhat in
       let iexp' = rename_init_exp ren iexp in
       (iwhat',iexp')
     in
     let iwhat_iexpL' = List.map f iwhat_iexpL in
     C.COMPOUND_INIT iwhat_iexpL'
and rename_decl_type ren decl_type =
  match decl_type with
 | C.JUSTBASE -> C.JUSTBASE
 | C.PARENTYPE (attrL0,decl_type0,attrL1) ->
    let decl_type0' = rename_decl_type ren decl_type0 in
    C.PARENTYPE (attrL0,decl_type0',attrL1)
 | C.ARRAY (decl_type0,attrL,exp0) ->
    let decl_type0' = rename_decl_type ren decl_type0 in
    let exp0' = rename_expression ren exp0 in    
    C.ARRAY (decl_type0',attrL,exp0')
 | C.PTR (attrL,decl_type0) ->
    let decl_type0' = rename_decl_type ren decl_type0 in
    C.PTR (attrL,decl_type0')
 | C.PROTO (decl_type0,single_nameL,b) ->
    let decl_type0' = rename_decl_type ren decl_type0 in
    let single_nameL' = List.map (rename_single_name ren) single_nameL in
    C.PROTO (decl_type0',single_nameL',b)
and rename_init_what ren init_what =
  match init_what with
  | C.NEXT_INIT -> C.NEXT_INIT
  | C.INFIELD_INIT (str,iwhat0) ->
     let iwhat0' = rename_init_what ren iwhat0 in
     C.INFIELD_INIT (str,iwhat0')
  | C.ATINDEX_INIT (exp0,iwhat0) ->
     let exp0' = rename_expression ren exp0 in
     let iwhat0' = rename_init_what ren iwhat0 in
     C.ATINDEX_INIT (exp0',iwhat0')
  | C.ATINDEXRANGE_INIT (exp0,exp1) ->
     let exp0' = rename_expression ren exp0 in
     let exp1' = rename_expression ren exp1 in
     C.ATINDEXRANGE_INIT (exp0',exp1')
;;


(*----------------------*)
(* Block transformation *)
(*----------------------*)
(*
(1) variable renaming: done by the above
(2) decl-init decomposition and extract declaration: 
    int x=1; -> x = 1 with recording "int x"
    int a[] = {1,2}; -> a[0]=1;a[1]=2; with recording "int a[2]"
(3) lifting declaration:
    {P1;int x;{P2;int y;P3};} -> {int x;int y; {P1;{P2;P3};} }
 *)


module MultiDimArray = struct
  (* For initialization of (multi-dimensional) arrays *)
  type t = B of C.expression | U of (t list)

  let rec from_initexp initexp =
    match initexp with
    | C.NO_INIT -> failwith "from_initexp: unexpected input (NO_INIT happens)"
    | C.SINGLE_INIT exp -> B exp
    | C.COMPOUND_INIT iwhat_iexpL ->
       let ee = 
         List.map
           (fun (iwhat,iexp) ->
             match iwhat with
             | C.NEXT_INIT -> from_initexp iexp
             | _ -> failwith "from_initexp: unexpected init_what (array)"
           )
           iwhat_iexpL
       in
       U ee

  let to_dim e : int list =
    let _res = ref [] in
    let rec aux e = 
      match e with
      | B _ -> ()
      | U ee ->
         let n = List.length ee in
         _res := n :: !_res;
         aux (List.hd ee)
    in
    aux e;
    List.rev !_res
    
  (* get dimension info from initialization of array : COMPOUND( {{1,2,3},{4,5,6}} ) -> [2;3] *)
  let get_dimension initexp : int list = to_dim (from_initexp initexp)

  let create_decl spec arrName initexp cloc cabsloc =
    let rec mkDecltype res idxL =
      match idxL with
      | [] -> res
      | n::idxL1 ->
         let res1 = C.ARRAY (res,[],C.CONSTANT (C.CONST_INT (string_of_int n))) in
         mkDecltype res1 idxL1
    in
    let idxL = get_dimension initexp in
    let decltype = mkDecltype C.JUSTBASE idxL in
    let name = (arrName,decltype,[],cloc) in
    C.DEFINITION (C.DECDEF ((spec,[(name,C.NO_INIT)]),cabsloc))
                                       
  (* create_asgn a [0;2] 3 makes a[0][2] = 3; *)
  let create_asgn eName (idxL: int list) eVal cloc = 
    let rec mkLval res idxL =
      match idxL with
      | [] -> res
      | n::idxL1 ->
         let res1 = C.INDEX (res, C.CONSTANT (C.CONST_INT (string_of_int n))) in
         mkLval res1 idxL1
    in
    let eLval = mkLval eName idxL in
    C.COMPUTATION (C.BINARY (C.ASSIGN,eLval,eVal),cloc)

  (* create_asgn a COMPOUND( {{1,2,3},{4,5,6}} ) makes a[0][0]=1;a[0][1]=2;..;a[1][2]=6; *)
  let create_asgnL eName initexp cloc =
    let e = from_initexp initexp in
    let _stmtL = ref [] in
    let _idxL = ref [] in
    let rec aux e =
      match e with
      | B eVal ->
         let stmt = create_asgn eName (List.rev !_idxL) eVal cloc in
         _stmtL := stmt :: !_stmtL
      | U ee ->
         for i = 0 to List.length ee - 1 do
           _idxL := i :: !_idxL;
           aux (List.nth ee i);
           _idxL := List.tl !_idxL
         done;
    in
    aux e;
    List.rev !_stmtL
    
end
;;

module MultiPointer = struct
  
  let create_asgn p decltype eVal cabsloc =
    let rec aux res decltype =
      match decltype with
      | C.JUSTBASE -> res
      | C.PTR (_,decltype1) ->
         let res1 = C.UNARY(C.MEMOF,res) in
         aux res1 decltype1
      | _ -> failwith "ctransform: create_asgn: unexpected decltype"
    in
    let exp = aux (C.VARIABLE p) decltype in
    C.COMPUTATION (C.BINARY (C.ASSIGN,exp,eVal),cabsloc)

end
;;

(* int x=1; -> ([int x],[x=1]) *)
(* int a[] = {1,2}; -> ([int a[2]],[a[0]=1;a[1]=2]) *)
let decompose_declinit_core spec name initexp cabsloc =
  let (v,decl_type,attrL,cloc) = name in    
  let mkDecl () = C.DEFINITION (C.DECDEF((spec,[(name,C.NO_INIT)]),cabsloc)) in
  let mkAsgn eVal = C.COMPUTATION (C.BINARY(C.ASSIGN,C.VARIABLE v,eVal), cabsloc) in
  match decl_type,initexp with
  | C.JUSTBASE,C.NO_INIT -> (* eg: int v; *)
     let sDecl = mkDecl () in
     ([sDecl], [])
  | C.JUSTBASE,C.SINGLE_INIT eVal -> (* eg: int v=1; *)
     let sDecl = mkDecl () in
     let sAsgn = mkAsgn eVal in
     ([sDecl],[sAsgn])
  | C.ARRAY _,C.NO_INIT -> (* eg: int a[2][3]; *)
     let sDecl = mkDecl () in
     ([sDecl], [])
  | C.ARRAY _,C.COMPOUND_INIT _ -> (* eg: int a[][]={{1,2,3};{4,5,6}}; or int a[2][3]={{1,2,3};{4,5,6}}; *)
     let eName = C.VARIABLE v in
     let sDecl = MultiDimArray.create_decl spec v initexp cloc cabsloc in
     let ssAsgn = MultiDimArray.create_asgnL eName initexp cloc in
     ([sDecl],ssAsgn)
  | C.PTR _,C.NO_INIT -> (* eg. int* y; *)
     let sDecl = mkDecl () in
     ([sDecl], [])
  | C.PTR _,C.SINGLE_INIT eVal -> (* eg: int* p = 10; *)
     let sDecl = mkDecl () in
     let sAsgn = MultiPointer.create_asgn v decl_type eVal cabsloc in
     ([sDecl], [sAsgn])
  | _,_ ->
     (* possible cases
    | C.PTR _,C.COMPOUND_INIT _ (* eg: struct A* a[2]= { str1,str2 }; *)
    | C.JUSTBASE _,C.COMPOUND_INIT _ (* eg: struct A p = {1,'a'}; *)
      they are just skipped 
     *)
     let init_name_group = (spec,[(name,initexp)]) in
     let s = C.DEFINITION (C.DECDEF(init_name_group,cabsloc)) in
     ([],[s])
;;

(* int x;y=1; -> ([int x;int y],[y=1])*)
let decompose_initnamegroup init_name_group cabsloc =
  let (spec,initnameL) = init_name_group in
  let pairL =
    List.map
      (fun (name,initexp) -> decompose_declinit_core spec name initexp cabsloc)
      initnameL
  in
  let ssDecl = List.flatten (List.map fst pairL) in
  let ssAsgn = List.flatten (List.map snd pairL) in
  (ssDecl,ssAsgn)
;;  
      
let rec decompDI_statement _ssDecl stmt =
  match stmt with
  | C.NOP _ -> stmt
  | C.BREAK _ -> stmt
  | C.CONTINUE _ -> stmt
  | C.GOTO (_,_) -> stmt
  | C.ASM _ -> stmt
  | C.BLOCK (blk,loc) ->
     let blk' = decompDI_block _ssDecl blk in
     C.BLOCK(blk',loc)
  | C.SEQUENCE (stmt1,stmt2,loc) ->
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     let stmt2' = decompDI_statement _ssDecl stmt2 in
     C.SEQUENCE (stmt1',stmt2',loc)
  | C.IF (exp,stmt1,stmt2,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     let stmt2' = decompDI_statement _ssDecl stmt2 in
     C.IF (exp',stmt1',stmt2',loc)
  | C.WHILE (fml,exp,stmt1,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.WHILE (fml,exp',stmt1',loc)
  | C.DOWHILE (fml,exp,stmt1,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.DOWHILE (fml,exp',stmt1',loc)
  | C.RETURN (exp,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     C.RETURN (exp',loc)
  | C.COMPUTATION (exp,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     C.COMPUTATION (exp',loc)
  | C.DEFAULT (stmt1,loc) ->
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.DEFAULT (stmt1',loc)
  | C.LABEL (lbl,stmt1,loc) ->
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.LABEL (lbl,stmt1',loc)
  | C.COMPGOTO (exp,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     C.COMPGOTO (exp',loc)
  | C.FOR (fml,for_cls,exp0,exp1,stmt2,loc) ->
     let for_cls' = decompDI_forcls _ssDecl for_cls in
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     let stmt2' = decompDI_statement _ssDecl stmt2 in
     C.FOR (fml,for_cls',exp0',exp1',stmt2',loc)
  | C.SWITCH (exp,stmt1,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.SWITCH (exp',stmt1',loc)
  | C.CASE (exp,stmt1,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     let stmt1' = decompDI_statement _ssDecl stmt1 in
     C.CASE (exp',stmt1',loc)
  | C.DEFINITION (C.DECDEF(init_name_group,cabsloc)) -> (* CORE CASE *)     
     let sNOP = C.NOP cabsloc in
     let rec toSeq ss = match ss with [] -> sNOP | [s] -> s | s::ss1 -> C.SEQUENCE(s,(toSeq ss1),cabsloc) in
     let (ssDecl,ssAsgn) = decompose_initnamegroup init_name_group cabsloc in
     _ssDecl := List_tailrec.append_rev ssDecl !_ssDecl;
     toSeq ssAsgn
  | C.DEFINITION def ->
     let def' = decompDI_definition _ssDecl def in
     C.DEFINITION def'
  | C.CASERANGE (exp0,exp1,stmt2,loc) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     let stmt2' = decompDI_statement _ssDecl stmt2 in
     C.CASERANGE (exp0',exp1',stmt2',loc)
  | C.TRY_EXCEPT (blk0,exp1,blk2,loc) ->
     let blk0' = decompDI_block _ssDecl blk0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     let blk2' = decompDI_block _ssDecl blk2 in
     C.TRY_EXCEPT (blk0',exp1',blk2',loc)
  | C.TRY_FINALLY (blk0,blk1,loc) ->
     let blk0' = decompDI_block _ssDecl blk0 in     
     let blk1' = decompDI_block _ssDecl blk1 in
     C.TRY_FINALLY (blk0',blk1',loc)
and decompDI_expression _ssDecl exp =
  match exp with
  | C.NOTHING -> exp
  | C.LABELADDR _ -> exp
  | C.CONSTANT _ -> exp
  | C.TYPE_SIZEOF _ -> exp
  | C.TYPE_ALIGNOF _ -> exp
  | C.EXPR_PATTERN str -> exp
  | C.VARIABLE v -> exp                        
  | C.UNARY (op,exp0) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.UNARY (op,exp0')
  | C.BINARY (binop,exp0,exp1) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     C.BINARY (binop,exp0',exp1')
  | C.QUESTION (exp0,exp1,exp2) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     let exp2' = decompDI_expression _ssDecl exp2 in
     C.QUESTION (exp0',exp1',exp2')
  | C.CAST ((spec,decl_type),initexp) ->
     let decl_type' = decompDI_decl_type _ssDecl decl_type in
     let initexp' = decompDI_init_expression _ssDecl initexp in
     C.CAST ((spec,decl_type'),initexp')
  | C.CALL (exp0,expL) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let expL' = List.map (decompDI_expression _ssDecl) expL in
     C.CALL (exp0',expL')
  | C.COMMA expL ->
     let expL' = List.map (decompDI_expression _ssDecl) expL in
     C.COMMA expL'
  | C.PAREN exp0 ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.PAREN exp0'
  | C.EXPR_SIZEOF exp0 ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.EXPR_SIZEOF exp0'
  | C.EXPR_ALIGNOF exp0 -> 
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.EXPR_ALIGNOF exp0'
  | C.INDEX (exp0,exp1) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     C.INDEX (exp0',exp1')
  | C.MEMBEROF (exp0,str) -> 
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.MEMBEROF (exp0',str)
  | C.MEMBEROFPTR (exp0,str) ->
     let exp0' = decompDI_expression _ssDecl exp0 in     
     C.MEMBEROFPTR (exp0',str)
  | C.GNU_BODY blk ->
     let blk' = decompDI_block _ssDecl blk in
     C.GNU_BODY blk'
and decompDI_init_expression _ssDecl initexp =
  match initexp with
  | C.NO_INIT -> initexp
  | C.SINGLE_INIT exp0 ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.SINGLE_INIT exp0'
  | C.COMPOUND_INIT iwhat_iexpL ->
     let f (iwhat,iexp) =
       let iexp' = decompDI_init_expression _ssDecl iexp in
       let iwhat' = decompDI_initwhat _ssDecl iwhat in
       (iwhat',iexp')
     in
     let iwhat_iexpL' = List.map f iwhat_iexpL in
     C.COMPOUND_INIT iwhat_iexpL'
and decompDI_initwhat _ssDecl iwhat =
  match iwhat with
  | C.NEXT_INIT -> iwhat
  | C.INFIELD_INIT (str,iwhat0) ->
     let iwhat0' = decompDI_initwhat _ssDecl iwhat0 in
     C.INFIELD_INIT (str,iwhat0')
  | C.ATINDEX_INIT (exp0,iwhat0) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let iwhat0' = decompDI_initwhat _ssDecl iwhat0 in
     C.ATINDEX_INIT (exp0',iwhat0')
  | C.ATINDEXRANGE_INIT (exp0,exp1) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     C.ATINDEXRANGE_INIT (exp0',exp1')
and decompDI_block _ssDecl blk =
     let blk' =
       {
         C.blabels = blk.C.blabels;
         C.battrs = blk.C.battrs;
         C.bstmts = List.map (decompDI_statement _ssDecl) blk.C.bstmts;
       }
     in
     blk'
and decompDI_forcls _ssDecl for_cls =
  match for_cls with
  | C.FC_EXP exp ->
     let exp' = decompDI_expression _ssDecl exp in
     C.FC_EXP exp'
  | C.FC_DECL def ->
     let def' = decompDI_definition _ssDecl def in     
     C.FC_DECL def'
and decompDI_definition _ssDecl def =
  match def with
  | C.GLOBASM _ -> def
  | C.ONLYTYPEDEF _ -> def
  | C.TYPEDEF _ -> def
  | C.PRAGMA (exp,loc) ->
     let exp' = decompDI_expression _ssDecl exp in
     C.PRAGMA (exp',loc)
  | C.LINKAGE (str,loc,defL) ->
     let defL' = List.map (decompDI_definition _ssDecl) defL in
     C.LINKAGE (str,loc,defL')
  | C.S_FUNDEF (fml0,fml1,def0,loc) ->
     let def0' = decompDI_definition _ssDecl def0 in
     C.S_FUNDEF (fml0,fml1,def0',loc)
  | C.TRANSFORMER (def0,defL,loc) ->
     let def0' = decompDI_definition _ssDecl def0 in
     let defL' = List.map (decompDI_definition _ssDecl) defL in
     C.TRANSFORMER (def0',defL',loc)
  | C.FUNDEF (single_name,blk,loc0,loc1) -> 
     let single_name' = decompDI_single_name _ssDecl single_name in
     let blk' = decompDI_block _ssDecl blk in     
     C.FUNDEF (single_name',blk',loc0,loc1)
  | C.S_INDDEF (indclauseL,loc) ->
     let indclauseL' = List.map (decompDI_indclause _ssDecl) indclauseL in
     C.S_INDDEF (indclauseL',loc)
  | C.DECDEF (init_name_group,loc) -> 
     let init_name_group' = decompDI_init_name_group _ssDecl init_name_group in
     C.DECDEF (init_name_group',loc)
  | C.EXPRTRANSFORMER (exp0,exp1,loc) -> 
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     C.EXPRTRANSFORMER (exp0',exp1',loc)
and decompDI_single_name _ssDecl single_name =
  single_name (* do nothing *)
and decompDI_indclause _ssDecl indclause =
  indclause (* do nothing *)
and decompDI_init_name_group _ssDecl init_name_group =
  let (tp, init_nameL) = init_name_group in
  let init_nameL' = List.map (decompDI_init_name _ssDecl) init_nameL in
  (tp, init_nameL')
and decompDI_init_name _ssDecl init_name =
  let (name,init_exp) = init_name in
  let name' = decompDI_name _ssDecl name in
  let init_exp' = decompDI_init_exp _ssDecl init_exp in
  (name',init_exp')
and decompDI_name _ssDecl name =
  let (v,decl_type,attrL,loc) = name in
  let decl_type' = decompDI_decl_type _ssDecl decl_type in
  (v,decl_type',attrL,loc)
and decompDI_init_exp _ssDecl init_exp =
  match init_exp with
  | C.NO_INIT -> init_exp
  | C.SINGLE_INIT exp0 ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     C.SINGLE_INIT exp0'
  | C.COMPOUND_INIT iwhat_iexpL ->
     let f (iwhat,iexp) =
       let iwhat' = decompDI_init_what _ssDecl iwhat in
       let iexp' = decompDI_init_exp _ssDecl iexp in
       (iwhat',iexp')
     in
     let iwhat_iexpL' = List.map f iwhat_iexpL in
     C.COMPOUND_INIT iwhat_iexpL'
and decompDI_decl_type _ssDecl decl_type =
  match decl_type with
 | C.JUSTBASE -> C.JUSTBASE
 | C.PARENTYPE (attrL0,decl_type0,attrL1) ->
    let decl_type0' = decompDI_decl_type _ssDecl decl_type0 in
    C.PARENTYPE (attrL0,decl_type0',attrL1)
 | C.ARRAY (decl_type0,attrL,exp0) ->
    let decl_type0' = decompDI_decl_type _ssDecl decl_type0 in
    let exp0' = decompDI_expression _ssDecl exp0 in    
    C.ARRAY (decl_type0',attrL,exp0')
 | C.PTR (attrL,decl_type0) ->
    let decl_type0' = decompDI_decl_type _ssDecl decl_type0 in
    C.PTR (attrL,decl_type0')
 | C.PROTO (decl_type0,single_nameL,b) ->
    let decl_type0' = decompDI_decl_type _ssDecl decl_type0 in
    let single_nameL' = List.map (decompDI_single_name _ssDecl) single_nameL in
    C.PROTO (decl_type0',single_nameL',b)
and decompDI_init_what _ssDecl init_what =
  match init_what with
  | C.NEXT_INIT -> C.NEXT_INIT
  | C.INFIELD_INIT (str,iwhat0) ->
     let iwhat0' = decompDI_init_what _ssDecl iwhat0 in
     C.INFIELD_INIT (str,iwhat0')
  | C.ATINDEX_INIT (exp0,iwhat0) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let iwhat0' = decompDI_init_what _ssDecl iwhat0 in
     C.ATINDEX_INIT (exp0',iwhat0')
  | C.ATINDEXRANGE_INIT (exp0,exp1) ->
     let exp0' = decompDI_expression _ssDecl exp0 in
     let exp1' = decompDI_expression _ssDecl exp1 in
     C.ATINDEXRANGE_INIT (exp0',exp1')
;;


(* int x=3; --> int x; x=3; *)
let initsplit_statement s =
  match s with
  | C.DEFINITION (C.DECDEF(init_name_group,cabsloc)) ->
     let sNOP = C.NOP cabsloc in
     let rec toSeq ss = match ss with [] -> sNOP | [s] -> s | s::ss1 -> C.SEQUENCE(s,(toSeq ss1),cabsloc) in
     let (ssDecl,ssAsgn) = decompose_initnamegroup init_name_group cabsloc in
     let ss= List_tailrec.append_rev ssDecl ssAsgn in
     toSeq ss
  | _ -> s
;;

let rec rename_liftdecl_loop s =
  match s with
  | C.BLOCK (blk,loc) ->
     let blk' = 
       {
         C.blabels = blk.C.blabels;
         C.battrs = blk.C.battrs;
         C.bstmts = List.map rename_liftdecl_loop blk.C.bstmts;
       }
     in
     C.BLOCK (blk',loc)
  | C.SEQUENCE (s0,s1,loc) ->
     let s0' = rename_liftdecl_loop s0 in
     let s1' = rename_liftdecl_loop s1 in
     C.SEQUENCE (s0',s1',loc)
  | C.IF (eCond,sThen,sElse,loc) ->
     let sThen' = rename_liftdecl_loop sThen in
     let sElse' = rename_liftdecl_loop sElse in
     C.IF (eCond,sThen',sElse',loc)
  | C.SWITCH (eCond, sBody, loc) ->
     let sBody' = rename_liftdecl_loop sBody in
     C.SWITCH (eCond,sBody',loc)
  | C.CASE (e,sBody,loc) ->
     let sBody' = rename_liftdecl_loop sBody in
     C.CASE (e,sBody',loc)
  | C.CASERANGE (e0,e1,sBody,loc) ->
     let sBody' = rename_liftdecl_loop sBody in
     C.CASERANGE (e0,e1,sBody',loc)
  | C.DEFAULT (sBody,loc) ->
     let sBody' = rename_liftdecl_loop sBody in
     C.DEFAULT (sBody',loc)
  | C.LABEL (str,sBody,loc) ->
     let sBody' = rename_liftdecl_loop sBody in
     C.LABEL (str,sBody',loc)
  | C.WHILE _ ->
     (* Local variable renaming *)
     let ren = Renamer.init () in
     let s' = rename_statement ren s in
     (* variable initialization splitting *)
     begin
       match initsplit_statement s' with
       | C.WHILE(fml,eCond,sBody,loc) ->
          (* Local-declaration lifting *)
          let _ssDecl = ref [] in
          let sBody1 = decompDI_statement _ssDecl sBody in
          begin
            match !_ssDecl with
            | [] -> C.WHILE(fml,eCond,sBody1,loc)
            | _ ->
               (* Make nested block for lifted local variable declarations *)
               let blk_inner =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = [C.WHILE(fml,eCond,sBody1,loc)];
                 }
               in
               let blk_outer =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
                 }
               in
               C.BLOCK(blk_outer,loc)
          end
       | _ -> failwith "dummy"
     end
  | C.DOWHILE _ ->
     (* Local variable renaming *)
     let ren = Renamer.init () in
     let s' = rename_statement ren s in
     (* variable initialization splitting *)
     begin
       match initsplit_statement s' with
       | C.DOWHILE (fml,eCond,sBody,loc) ->
          (* Local-declaration lifting *)
          let _ssDecl = ref [] in
          let sBody1 = decompDI_statement _ssDecl sBody in
          begin
            match !_ssDecl with
            | [] -> C.DOWHILE(fml,eCond,sBody1,loc)
            | _ ->
               (* Make nested block for lifted local variable declarations *)
               let blk_inner =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = [C.DOWHILE(fml,eCond,sBody1,loc)];
                 }
               in
               let blk_outer =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
                 }
               in
               C.BLOCK(blk_outer,loc)
          end
       | _ -> failwith "dummy"
     end
  | C.FOR _ ->
     (* Local variable renaming *)
     let ren = Renamer.init () in
     let s' = rename_statement ren s in
     (* variable initialization splitting *)
     begin
       match initsplit_statement s' with
       | C.FOR (fml,fcls,e0,e1,sBody,loc) ->
          (* Local-declaration lifting *)
          let _ssDecl = ref [] in
          let sBody1 = decompDI_statement _ssDecl sBody in
          begin
            match !_ssDecl with
            | [] -> C.FOR (fml,fcls,e0,e1,sBody1,loc)
            | _ ->
               (* Make nested block for lifted local variable declarations *)
               let blk_inner =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = [C.FOR (fml,fcls,e0,e1,sBody1,loc)];
                 }
               in
               let blk_outer =
                 {
                   C.blabels = [];
                   C.battrs = [];
                   C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
                 }
               in
               C.BLOCK(blk_outer,loc)
          end
       | _ -> failwith "dummy"
     end         
 | _ -> s
;;

(*--------------------------------
Block
- splitting a block
---------------------------------*)
(* split_list cond f [a;b;c;d;e] returns [[a;b];[f(c)];[d;e]] if c satisfies cond *)
let splitList cond f ll =
  let rec splitrec tmp result ls =
    match ls with
    | [] -> if tmp = [] then result else (List.rev tmp) :: result
    | x::xl when cond x ->
       if tmp = []
       then splitrec [] ([f(x)]::result) xl
       else splitrec [] ([f(x)]::(List.rev tmp)::result) xl
    | x::xl ->
       splitrec (x::tmp) result xl
  in
  List.rev (splitrec [] [] ll)
;;  

module StmtL = struct
  (* ss is used *)
  type t = C.statement list

  let fromStmt stmt : t =
    match stmt with
(*
    | C.BLOCK(block,_) -> setminus block.C.bstmts [_Nop]
    | C.NOP _ -> []
 *)
    | C.BLOCK(block,_) -> block.C.bstmts
    | _ -> [stmt]

  let print (ss : t) =
    List.iter print_statement ss

end
;;
module SS = StmtL
;;

module MyBlock = struct
  (* [ [s1;s2]; [break]; [s3;s4]; [if-cont]; [s5] ] is a block *)
  (* [s1;s2;break;s3;s4;if-cont;s5] *)
  type t = SS.t list
         
  let create blk : t = splitList isLoopControl (fun x -> x) blk

  let toSS (sss : t) = List.flatten sss
    
  let print (sss : t) = SS.print (toSS sss)
    
end
;;
module MB = MyBlock
;;

module AnnotatedSS = struct

  type t =
    {
      mutable label : string;
      mutable body : SS.t;
      mutable annotation : C.expression list;
      mutable loc : C.cabsloc;
    }

  let decomp a = (a.label,a.body,a.annotation)
               
  let create l ss ee loc = { label = l; body = ss; annotation = ee; loc = loc }

  let getloc a =
    match a.body with
    | [] -> dmy_cabsloc
    | s::_ -> getloc s
                     
  let toSS a =
    if a.label = "" then a.body else (_Label0 (a.label) a.loc) :: a.body
    
  let print a =
    let labelstr = if a.label = "" then "no_label:\n" else (a.label ^ ":\n") in
    print_bytes labelstr;
    SS.print a.body;
    List.iter (fun exp -> print_expression exp; print_newline ()) a.annotation
    
  let separateLoopControl a =
    let ss = a.body in
    let sss = splitList isLoopControl (fun s->s) ss in
    match sss with
    | [] -> []
    | ss1::sss1 ->
       let a1 = create a.label ss1 [] a.loc in
       let aa1 = List.map (fun ssX -> create "" ssX [] a.loc) sss1 in
       a1::aa1
    
end
;;
module A = AnnotatedSS
;;
let isLoopControlRawA a = isLoopControlRawL a.A.body;;
let isLoopControlA a = isLoopControlL a.A.body;;
let isContinueA a = isContinueL a.A.body;;
let isReturnA a = isReturnL a.A.body;;
let isBreakA a = isBreakL a.A.body;;
let checkLoopControlA a = checkLoopControlL a.A.body;;

module AnnotatedMyBlock = struct
  (* 
    [  
        ("",ss0,[e0]);
        (L0,[if_continue],[]);
        ("",ss1);
        (L1,[return v],[e1]); 
        ("",ss2,[]); 
        (L2,[if_break],[e2])
    ] 
*)
  type t = AnnotatedSS.t list

  let putLabels (aa : t) : t =
    for i = 0 to List.length aa - 1 do
      let ai = List.nth aa i in
      match isLoopControlA ai && ai.A.label = "" with
      | true -> 
         ai.A.label <- genLabelName ();
      | false -> ()
    done;
    aa
    
  let toSS (aa : t) : SS.t = List.flatten (List.map A.toSS aa)

  let cutUnreachable (aa : t) : t =
    let rec aux res aa0 =
      match aa0 with
      | [] -> List.rev res
      | a::_ when isLoopControlRawA a -> List.rev (a::res)
      | a::aa1 -> aux (a::res) aa1
    in
    aux [] aa

  let cutUnreachableAndLastContinue (aa : t) : t =
    let rec aux res aa0 =
      match aa0 with
      | [] -> List.rev res
      | a::_ when isContinueA a -> List.rev res
      | a::_ when isLoopControlRawA a -> List.rev (a::res)
      | a::aa1 -> aux (a::res) aa1
    in
    aux [] aa    

  let separateLoopControl (aa : t) : t =
    List.flatten (List.map A.separateLoopControl aa)

  (* fromStmt produces annot.SS list from a stmt *)
  (* Note: blocks should be flatten *)
  let rec fromStmt s : t =
    let ss = SS.fromStmt s in
    let loc = getloc s in
    let a = A.create "" ss [] loc in
    separateLoopControl [a]
    
  let removeByLabel rlabel (aa : t) =
    let rec aux res aa0 =
      match aa0 with
      | [] -> List.rev res
      | a1::aa1 when a1.A.label = rlabel -> aux res aa1
      | a1::aa1 -> aux (a1::res) aa1
    in
    aux [] aa
    
  let print (aa : t) = List.iter A.print aa

end
;;
module AA = AnnotatedMyBlock
;;
let aa2stmt (aa : AA.t) =
  let ss = AA.toSS aa in
  ss2stmt ss
;;
let _IfAA eCond aaThen aaElse = _If eCond (aa2stmt aaThen) (aa2stmt aaElse)
;;
let _IfThenAA eCond aaThen = _If eCond (aa2stmt aaThen) _Nop
;;
let _WhileAA eCond aaBody = _While eCond (aa2stmt aaBody)
;;
let _DoWhileAA eCond aaBody = _DoWhile eCond (aa2stmt aaBody)
;;

(* Elimination of IfContinue *)
let elimIfContinue (aaBody : AA.t) : AA.t = 
  let _cond = ref [] in
  let _res = ref [] in
  for i = 0 to List.length aaBody - 1 do
    let ai = List.nth aaBody i in
    let (_L,ss,ee) = A.decomp ai in
    match checkLoopControlA ai with
    | IFCONTINUE (eCond,loc) ->
       let a1 = A.create _L [] [] loc in
       _cond := (_Not eCond |@| _L) :: !_cond;
       _res := a1 :: !_res
    | IFBREAK (eCond,loc) ->
       let eCond1 = bigAnd (eCond :: !_cond) in
       let stmt = _IfBreak eCond1 loc in
       let a1 = A.create _L [stmt] ee loc in
       _res := a1 :: !_res
    | IFRETURN (eCond,eVal,loc) ->
       let eCond1 = bigAnd (eCond :: !_cond) in
       let stmt = _IfReturn eCond1 eVal loc in
       let a1 = A.create _L [stmt] ee loc in
       _res := a1 :: !_res
    | _ ->
       if !_cond = []
       then
         _res := ai :: !_res
       else
         begin
           let loc = A.getloc ai in
           let eCond1 = bigAnd !_cond in
           (*           let stmt = _IfThenSS eCond1 ss in *)
           let stmt = _IfThenSS eCond1 ss loc in
           let a1 = A.create _L [stmt] ee loc in
           _res := a1 :: !_res
         end
  done;
  List.rev !_res
;;

(* putting Annotations *)
(* assmumption: all If-continue/continue are already eliminated *)
let putAnnotation (aaBody : AA.t) = 
  let _aaResult = ref [] in
  let _eeAnot = ref [] in
  for i = 0 to List.length aaBody - 1 do
    let ai = List.nth aaBody i in
    let (_L,ss,_) = A.decomp ai in
    match checkLoopControlA ai with
    | IFBREAK (eCond,loc) ->
       let a1 = A.create _L ss !_eeAnot loc in
       let eAnot = (_Not eCond) |@| _L in
       _eeAnot := [ bigAnd (eAnot :: !_eeAnot) ] ;
       _aaResult := a1 :: !_aaResult
    | IFRETURN (eCond,eVal,loc) ->
       let a1 = A.create _L ss !_eeAnot loc in
       let eAnot = (_Not eCond) |@| _L in
       _eeAnot := [ bigAnd (eAnot :: !_eeAnot) ] ;
       _aaResult := a1 :: !_aaResult
    | _ ->
       let ai' = A.create _L ss !_eeAnot ai.A.loc in
       _aaResult := ai' :: !_aaResult
  done;
  List.rev !_aaResult
;;

(* eliminating Break/Return *)
(* assmumption: all If-continue/continue are already eliminated *)
let elimBreakReturn (aaBody : AA.t) =
  let aaBody1 = List.rev aaBody in
  let _aaResult = ref [] in
  let _aaReturn = ref [] in
  let lastAnnot = if aaBody = [] then [] else (List.hd aaBody1).A.annotation in
  for i = 0 to List.length aaBody1 - 1 do
    let ai = List.nth aaBody1 i in
    let (_L,ss,eeAnot) = A.decomp ai in
    match checkLoopControlA ai with
    | BREAK _ -> ()
    | RETURN (eVal,loc) ->
       let eCond = bigAnd eeAnot in
       let s_ret = _IfThenSS eCond [_Return eVal loc] loc in
       let a_ret = A.create "" [s_ret] [] loc in
       _aaReturn := a_ret :: !_aaReturn;
    | IFBREAK (eCond,loc) ->
       let eCond1 = bigAnd @@ ((_Not eCond) |@| _L) :: eeAnot in
       let stmt = _IfThenAA eCond1 (AA.removeByLabel "dummy" !_aaResult) loc in
       let a = A.create _L [stmt] [] loc in
       _aaResult := [ a ]
    | IFRETURN (eCond,eVal,loc) ->
       let eCond0 = bigAnd @@ ((_Not eCond) |@| _L) :: eeAnot in
       let stmt0 = _IfThenAA eCond0 (AA.removeByLabel "dummy" !_aaResult) loc in
       let a0 = A.create _L [stmt0] eeAnot loc in
       _aaResult := [ a0 ];
       let eCond1 = bigAnd @@ (eCond |@| _L) :: eeAnot in
       let s_ret1 = _IfThenSS eCond1 [_Return (eVal |@| _L) loc] loc in
       let a_ret1 = A.create "" [s_ret1] [] loc in
       _aaReturn := a_ret1 :: !_aaReturn;       
    | _ ->
       let a = A.create _L ss [] ai.A.loc in
       _aaResult := a :: !_aaResult;       
  done;
  (!_aaResult, !_aaReturn, lastAnnot)
;;



(*--------------------------------------*)
(* Transformation of If                 *)
(* Assumption:                          *)
(* aaThen and aaElse are already in NF  *)
(*--------------------------------------*)
let transIfCoreLabel _L eCond aaThen aaElse loc =
  let _i = ref 0 in
  let _aaThen = ref (AA.removeByLabel "dummy" aaThen) in
  let _aaElse = ref (AA.removeByLabel "dummy" aaElse) in
  let _ssBody = ref [] in (* current body of output *)
  let pp () =
    let stmt = _IfAA eCond !_aaThen !_aaElse loc in
    print_statement stmt;
    print_newline ();
  in
  let pp_mes mes =
    let header = "transIfCoreLabel: " in
    print_endline (header ^ mes)
  in
  
  doIfDebug pp_mes "ORIGINAL Input ----------------";
  doIfDebug pp ();
  
  doIfDebug pp_mes "Separating Controls -------";
  _aaThen := AA.separateLoopControl !_aaThen;
  if !_aaElse = [] then () else _aaElse := AA.separateLoopControl !_aaElse;
  doIfDebug pp ();
  
  doIfDebug pp_mes "Unreachable elimination -------";  
  _aaThen := AA.cutUnreachable !_aaThen;
  _aaElse := AA.cutUnreachable !_aaElse;
  doIfDebug pp ();
  
  (* Splitting Then-part  *)  
  let _aaThenTop = ref [] in
  let aaThen = !_aaThen in
  let lenThen = List.length aaThen in
  _i := 0;
  while (!_i < lenThen) && not(isLoopControlA (List.nth aaThen !_i)) do
    _aaThenTop := (List.nth aaThen !_i) :: !_aaThenTop;
    _aaThen := List.tl !_aaThen;
    _i := !_i + 1;
  done;
  _aaThenTop := List.rev !_aaThenTop;
  
  (* Splitting Else-part  *)
  let _aaElseTop = ref [] in
  let aaElse = !_aaElse in
  let lenElse = List.length !_aaElse in
  _i := 0;
  while (!_i < lenElse) && not(isLoopControlA (List.nth aaElse !_i)) do
    _aaElseTop := (List.nth aaElse !_i) :: !_aaElseTop;
    _aaElse := List.tl !_aaElse;
    _i := !_i + 1;
  done;
  _aaElseTop := List.rev !_aaElseTop;

  (* Making top-if *)  
  begin
    match !_aaThenTop,!_aaElseTop with
    | [],[] -> ()
    | _,_ ->
       let stmt = _IfAA eCond !_aaThenTop !_aaElseTop loc in
       _ssBody := [stmt];
  end;

  (* Making Then-part *)    
  let eCondThen ee = bigAnd @@ (eCond |@| _L) :: ee in
  for j = 0 to List.length !_aaThen - 1 do
    let aj = List.nth !_aaThen j in
    match checkLoopControlA aj with
    | IFBREAK (e,loc) ->
       let stmt = _IfThenSS (eCondThen [e]) [_Break loc] loc in
       _ssBody := stmt :: !_ssBody
    | IFCONTINUE (e,loc) ->
       let stmt = _IfThenSS (eCondThen [e]) [_Continue loc] loc in
       _ssBody := stmt :: !_ssBody
    | IFRETURN (e,eVal,loc) ->
       let stmt = _IfThenSS (eCondThen [e]) [_Return eVal loc] loc in
       _ssBody := stmt :: !_ssBody
    | _ ->
       let loc = aj.A.loc in
       let stmt = _IfThenAA (eCondThen []) [aj] loc in
       _ssBody := stmt :: !_ssBody
  done;

  (* Making Else-part *)      
  let eCondElse ee = bigAnd @@ ((_Not eCond) |@| _L) :: ee in
  for j = 0 to List.length !_aaElse - 1 do
    let aj = List.nth !_aaElse j in
    match checkLoopControlA aj with
    | IFBREAK (e,loc) ->
       let stmt = _IfThenSS (eCondElse [e]) [_Break loc] loc in
       _ssBody := stmt :: !_ssBody
    | IFCONTINUE (e,loc) ->
       let stmt = _IfThenSS (eCondElse [e]) [_Continue loc] loc in
       _ssBody := stmt :: !_ssBody
    | IFRETURN (e,eVal,loc) ->
       let stmt = _IfThenSS (eCondElse [e]) [_Return eVal loc] loc in
       _ssBody := stmt :: !_ssBody
    | _ ->
       let loc = aj.A.loc in
       let stmt = _IfThenAA (eCondElse []) [aj] loc in
       _ssBody := stmt :: !_ssBody
  done;  

  (* Result *)
  doIfDebug pp_mes "Result --------------------------";
  _ssBody := List.rev !_ssBody;
  let aaResult = [ A.create _L !_ssBody [] loc ] in
  doIfDebug AA.print aaResult;
  aaResult
;;

let transIfCore eCond aaThen aaElse loc =
  let _L = genLabelName () in
  let _aaThen = ref (AA.removeByLabel "dummy" aaThen) in
  let _aaElse = ref (AA.removeByLabel "dummy" aaElse) in
  match !loop_depth with
  | 0 ->
     _aaThen := AA.cutUnreachable !_aaThen;
     _aaElse := AA.cutUnreachable !_aaElse;     
     let stmt = _IfAA eCond !_aaThen !_aaElse loc in
     let aaResult = [ A.create "" [stmt] [] loc ] in
     aaResult
  | _ ->
     transIfCoreLabel _L eCond aaThen aaElse loc
;;


(*-------------------------------------------------*)
(* Transformation of While                         *)
(* Assumption                                      *)
(* aaBody is already in Normal Form                *)
(* dowhileflag = true: it is used for do-while     *)
(*-------------------------------------------------*)
(* Dummy annoted-statements *)
(* It will put at the last position of a loop-body *)
(* Its role is to obtain the last annotation *)
let aDummy = A.create "dummy" [_Nop] [] dmy_cabsloc
;;

let transWhileCore dowhileflag eCond (aaBody : AA.t) loc : AA.t =
  let label0 = genLabelName () in
  let _onceFlag = ref false in
  let _aaBody = ref aaBody in 
  let pp () =
    let stmt = _WhileAA eCond !_aaBody loc in
    print_statement stmt;
    print_newline ();
  in
  let pp_mes mes =
    let header = "transWhile: " in
    print_endline (header ^ mes)
  in
  
  doIfDebug pp_mes "Input ----------------";
  doIfDebug pp ();

  doIfDebug pp_mes "Separating -------";
  _aaBody := AA.separateLoopControl !_aaBody;
  doIfDebug pp ();

  doIfDebug pp_mes "Unreachable + Last continue elimination -------";
  _aaBody := AA.cutUnreachableAndLastContinue !_aaBody;
  doIfDebug pp ();
  
  let sssBody0 = List.map (fun a -> a.A.body) !_aaBody in
  begin
    match List.exists isLoopControlRawL sssBody0 with
    | true -> _onceFlag := true;
    | false -> ()
  end;
  
  doIfDebug pp_mes "Putting Labels ----------------";
  _aaBody := AA.putLabels !_aaBody;
  doIfDebug pp ();
  
  doIfDebug pp_mes "If-continue elimination -------";
  _aaBody := elimIfContinue !_aaBody;
  doIfDebug pp ();
  
  doIfDebug pp_mes "Put annotations --------------";
  _aaBody := !_aaBody @ [aDummy];
  _aaBody := putAnnotation !_aaBody;
  doIfDebug pp ();

  doIfDebug pp_mes "Break/Return elimination -----";
  let (aaBodyA,aaReturnA,eeAnnotA) = elimBreakReturn !_aaBody in
  _aaBody := AA.removeByLabel "dummy" aaBodyA;
  doIfDebug pp ();
  (*
  doIfDebug AA.print !_aaBody;
  doIfDebug pp_mes "Return part --";
  doIfDebug AA.print aaReturnA;
   *)
  
  match !_onceFlag with
  | true -> (* perform while-elimination *)
     doIfDebug pp_mes "This while is done once";
     doIfDebug pp_mes "--> (the result of transIf) will be returned";
     let aaIf = transIfCoreLabel label0 eCond !_aaBody [] loc in
     doIfDebug pp_mes "Result =======================";
     aaIf @ aaReturnA
  | false -> (* perform while-unfolding *)
     doIfDebug pp_mes "This while is done more than one";
     doIfDebug pp_mes "--> (the result of transIf);(the result of transWhile) will be returned";
     let aaIf = if dowhileflag
                then []
                else transIfCoreLabel label0 eCond !_aaBody [] loc
     in
     let eeCondWhile = if dowhileflag
                       then [eCond]
                       else eCond :: (eCond |@| label0) :: eeAnnotA
     in
     let eCondWhile = bigAnd eeCondWhile in
     let sTopWhile = _WhileAA eCondWhile !_aaBody loc in
     let aaTopWhile = [ A.create "" [sTopWhile] [] loc ] in
     doIfDebug pp_mes "Result ----";
     let aaResult = aaIf @ aaTopWhile @ aaReturnA in
     doIfDebug AA.print aaResult;
     aaResult
;;

(*-------------------------------------------------*)
(* Transformation of Do-While                      *)
(* Assumption                                      *)
(* aaBody is already in Normal Form                *)
(*-------------------------------------------------*)
let transDoWhileCore eCond (aaBody : AA.t) loc : AA.t =
  let label0 = genLabelName () in
  let _onceFlag = ref false in
  let _aaResult = ref [] in
  let _aaBody = ref aaBody in
  let _aaWhile = ref [] in
  let pp_before () =
    let stmt = _DoWhileAA eCond !_aaBody loc in
    print_statement stmt;
    print_newline ()
  in
  let pp_after () =
    let sWhile = _WhileAA eCond !_aaBody loc in
    let aWhile = A.create "" [sWhile] [] loc in
    AA.print @@ !_aaBody @ [ aWhile ];
    print_newline ();
  in  
  let pp_mes mes =
    let header = "transDoWhile: " in
    print_endline (header ^ mes)
  in
  doIfDebug pp_mes "Input ----------------";
  doIfDebug pp_before ();
  
  try
    doIfDebug pp_mes "Separating -------";
    _aaBody := AA.separateLoopControl !_aaBody;
    doIfDebug pp_before ();

    doIfDebug pp_mes "Unreachable + Last-continue elimination -------";
    _aaBody := AA.cutUnreachableAndLastContinue !_aaBody;
    let tmpBody = List.rev !_aaBody in
    if tmpBody <> [] && (isBreakA (List.hd tmpBody) || isReturnA (List.hd tmpBody))
    then
      begin
        doIfDebug pp_mes "The do-while loop finishes immediately by break/return";
        _aaResult := List.rev (List.tl tmpBody);
        raise Out
      end
    else
      doIfDebug pp_before ();

    let sssBody0 = List.map (fun a -> a.A.body) !_aaBody in
    begin
      match List.exists isLoopControlRawL sssBody0 with
      | true -> _onceFlag := true
      | false -> ()
    end;

    doIfDebug pp_mes "Putting Labels ----------------";
    _aaBody := AA.putLabels !_aaBody;
    doIfDebug pp_after ();

    doIfDebug pp_mes "If-continue elimination -------";
    _aaBody := elimIfContinue !_aaBody;
    doIfDebug pp_after ();

    doIfDebug pp_mes "Put annotations --------------";
    _aaBody := !_aaBody @ [aDummy];
    _aaBody := putAnnotation !_aaBody;
    doIfDebug pp_after ();

    doIfDebug pp_mes "Break/Return elimination -----";
    let (aaBodyA,aaReturnA,eeAnnotA) = elimBreakReturn !_aaBody in
    _aaBody := AA.removeByLabel "dummy" aaBodyA;
    _aaResult := aaBodyA @ aaReturnA;

    (*-----------------_*)
    match !_onceFlag with
    | true -> (* perform do-while elimination *)
       let aaIf = transIfCoreLabel label0 eCond !_aaBody [] loc in
       _aaResult := aaIf @ aaReturnA;
       doIfDebugLazy AA.print (fun _ -> !_aaResult);
       raise Out
    | false -> (* perform do-while unfolding *)
       let eeCondWhile = eCond :: eeAnnotA in
       let eCondWhile = bigAnd eeCondWhile in
       let sTopWhile = _WhileAA eCondWhile !_aaBody loc in
       let aaTopWhile = [ A.create "" [sTopWhile] [] loc ] in
       _aaResult := !_aaBody @ aaTopWhile @ aaReturnA;
       doIfDebugLazy AA.print (fun _ -> !_aaResult);       
       raise Out
    (*-----------------*)
  with
    Out ->
    begin
      doIfDebug pp_mes "Result =======================";
      doIfDebugLazy AA.print (fun _ -> !_aaResult);
      !_aaResult
    end
;;

(*-----------------------------------*)
(* Transformation of For-statement   *)
(* Assumption                        *)
(* aaBody is already in Normal Form  *)
(*-----------------------------------*)
let transForCore forCls eCond eDiff sBody loc : C.statement * AA.t =
  let eCond' = if eCond = C.NOTHING then eTrue else eCond in
  let pp_mes mes =
    let header = "transFor: " in
    print_endline (header ^ mes)
  in
  let pp_before () =
    print_endline "For cond:";
    print_expression eCond';
    print_endline "For diff:";
    print_expression eDiff;
    print_endline "\nfor Body:";
    print_statement sBody;
    print_endline "endfor";    
  in
  doIfDebug pp_mes "Input ----------------";
  doIfDebug pp_before ();
  (* head part*)
  let sHead =
    match forCls with
    | C.FC_EXP exp -> C.COMPUTATION (exp, loc)
    | C.FC_DECL def -> C.DEFINITION def
  in
(* body becomes while *)
  let aaWhileBody = 
    let ssBody = SS.fromStmt sBody in
    let sDiff = C.COMPUTATION (eDiff,loc) in
    let aBody = A.create "" (ssBody @ [sDiff]) [] loc in
    [aBody]
  in
  (sHead, transWhileCore false eCond' aaWhileBody loc)
;;


(*--------------------------------------*)
(* Transformation of Switch-statement   *)
(* Assumption                           *)
(* aaBody is already in Normal Form     *)
(*--------------------------------------*)
let transSwitchCore eCond ssBody loc = 
  let pp_mes mes =
    let header = "transSwitch: " in
    print_endline (header ^ mes)
  in
  let pp_before () =
    print_endline "Switch cond:";
    print_expression eCond;
    print_endline "\nfor Body:";
    SS.print ssBody;
    print_endline "endSwitch";
  in
  doIfDebug pp_mes "Input ----------------";
  doIfDebug pp_before ();
  (* body *)
  let _BodyList = ref [] in
  (* it will contain (b,labels,body): b=false if non-labeled stmt, b=true if labeled stmt *)
  for i = 0 to List.length ssBody - 1 do
    let s = List.nth ssBody i in
    match s with
    | C.DEFAULT (sCaseBody,loc) -> 
       _BodyList := (true,[],sCaseBody,loc) :: !_BodyList      
    | C.CASE (eCaseLabel,sCaseBody,loc) ->
       _BodyList := (true,[eCaseLabel],sCaseBody,loc) :: !_BodyList
    | _ ->
       let loc = getloc s in
       _BodyList := (false,[],s,loc) :: !_BodyList
  done;
  _BodyList := List.rev !_BodyList;
  let _tmp = ref [] in
  let _splitRes = ref [] in
  let _eePrevLabel = ref [] in
  let _j = ref 0 in
  for i = 0 to List.length !_BodyList - 1 do
    match List.nth !_BodyList i with
    | (false,_,sCaseBody,_) -> ()
    | (true,eeLabel,sCaseBody,_) ->
       _tmp := [sCaseBody];
       _j := i + 1;
       while !_j < List.length !_BodyList && not (isBreak (thd4 (List.nth !_BodyList !_j))) do
         let (_,_,s,_) = List.nth !_BodyList !_j in
         _tmp := s :: !_tmp;
         _j := !_j + 1;
       done;
       
       _splitRes := (eeLabel, !_eePrevLabel, List.rev !_tmp) :: !_splitRes;
       _eePrevLabel := eeLabel @ !_eePrevLabel
  done;
  _splitRes := List.rev !_splitRes;
  
  (* creating translated statements *)
  let _L = genLabelName () in
  let aHead = A.create _L [] [] loc in
  let _result = ref [aHead] in
  for i = 0 to List.length !_splitRes - 1 do
    let (eeLabel,eePrevLabel,ss) = List.nth !_splitRes i in
    match eeLabel with
    | [] -> (* the case of DEFAULT *)
       let eCondIf0 = bigAnd @@ List.map (fun e -> eCond |<>| e) !_eePrevLabel in
       let eCondIf1 = eCondIf0 |@| _L in
       let aBodyIf = A.create "" ss [] loc in
       let aaIf = transIfCoreLabel "" eCondIf1 [aBodyIf] [] loc in
       _result := !_result @ aaIf
    | eLabel::_ -> (* the case of CASE *)
       let eCondIfHead = eCond |=| eLabel in
       let eeCondIfTail = List.map (fun e -> eCond |<>| e) eePrevLabel in
       let eCondIf0 = bigAnd @@ eCondIfHead :: eeCondIfTail in
       let eCondIf1 = eCondIf0 |@| _L in
       let aBodyIf = A.create "" ss [] loc in
       let aaIf = transIfCoreLabel "" eCondIf1 [aBodyIf] [] loc in
       _result := !_result @ aaIf
  done;
  !_result
;;



(*----------------------------------------*)
(* Elimination of the ternary operator    *)
(*----------------------------------------*)
(* 
(1) x = b ? e1 : e2 is replaced by
    if(b) { x = b; } else { x = e2; }
(2) int x = b ? e1 : e2 is replaced by
    int x; if(b) { x = b; } else { x = e2; }
 *)

let elimParen e =
  match e with
  | C.PAREN e1 -> e1
  | _ -> e
;;
let rec elimTernaryOne s : C.statement list =
  match s with
  | C.COMPUTATION(C.BINARY(C.ASSIGN,C.VARIABLE v,C.QUESTION(b,e1,e2)),loc) ->
     let e1' = elimParen e1 in
     let e2' = elimParen e2 in
     let ss1 = elimTernaryOne (v |:=| (e1',loc)) in
     let ss2 = elimTernaryOne (v |:=| (e2',loc)) in
     let sResult: C.statement = _If b (List.hd ss1) (List.hd ss2) loc in
     [sResult]
  | C.DEFINITION(C.DECDEF((spectypeL,initnameL),loc)) ->
     let spectype = List.hd spectypeL in
     List.flatten (List.map (transInitNameOne spectype loc) initnameL)
  | _ -> [s]
                                                   
and transInitNameOne spectype loc initname =
  let (name,init_expr) = initname in
  let (v,_,_,_) = name in
  match init_expr with
  | C.SINGLE_INIT(C.QUESTION(b,e1,e2)) ->
     let sDecl = _VarDecl spectype v loc in
     let ss1 = elimTernaryOne (v |:=| (e1,loc)) in
     let ss2 = elimTernaryOne (v |:=| (e2,loc)) in
     let sBody = _If b (List.hd ss1) (List.hd ss2) loc in
     [sDecl;sBody]
  | _ ->
     let sDecl = C.DEFINITION (C.DECDEF(([spectype],[initname]),loc)) in
     [sDecl]
;;

(*----------------------------------------*)
(* Elimination of the ternary operator2   *)
(*----------------------------------------*)
let rec elimTernaryE e =
  (* returns (e',[(z,b?e1:e2)]) *)
  match e with
  | C.QUESTION (b,e1,e2) -> 
     let (e1',vqL1) = elimTernaryE e1 in
     let (e2',vqL2) = elimTernaryE e2 in
     let eQ = C.QUESTION (b,e1',e2') in
     let v = genVarName () in
     (eVar v, vqL1 @ vqL2 @ [(v,eQ)])
  | C.UNARY(op,e0) ->
     let (e0',vqL1) = elimTernaryE e0 in
     let e' = C.UNARY(op,e0') in
     (e',vqL1)
  | C.BINARY(op,e1,e2) ->
     let (e1',vqL1) = elimTernaryE e1 in
     let (e2',vqL2) = elimTernaryE e2 in
     let e' = C.BINARY(op,e1',e2') in
     (e',vqL1 @ vqL2)
  | C.CALL(e0,ee0) ->
     let (ee0',vqL') = elimTernaryEE ee0 in
     let e' = C.CALL(e0,ee0') in
     (e',vqL')
  | C.COMMA ee ->
     let (ee',vqL') = elimTernaryEE ee in
     let e' = C.COMMA ee' in
     (e',vqL')     
  | C.PAREN e0 ->
     let (e0',vqL') = elimTernaryE e0 in
     let e' = C.PAREN e0' in
     (e',vqL')
  | C.EXPR_SIZEOF e0 -> 
     let (e0',vqL') = elimTernaryE e0 in
     let e' = C.EXPR_SIZEOF e0' in
     (e',vqL')
  | C.EXPR_ALIGNOF e0 -> 
     let (e0',vqL') = elimTernaryE e0 in
     let e' = C.EXPR_ALIGNOF e0' in
     (e',vqL')
  | C.INDEX(e1,e2) -> 
     let (e1',vqL1) = elimTernaryE e1 in
     let (e2',vqL2) = elimTernaryE e2 in
     let e' = C.INDEX(e1',e2') in
     (e',vqL1 @ vqL2)
  | C.MEMBEROF(e0,str) ->
     let (e0',vqL') = elimTernaryE e0 in
     let e' = C.MEMBEROF(e0',str) in
     (e',vqL')
  | C.MEMBEROFPTR(e0,str) ->
     let (e0',vqL') = elimTernaryE e0 in
     let e' = C.MEMBEROFPTR(e0',str) in
     (e',vqL')
  | C.NOTHING
    | C.LABELADDR _
    | C.CONSTANT _
    | C.VARIABLE _
    | C.TYPE_ALIGNOF _
    | C.TYPE_SIZEOF _
    | C.EXPR_PATTERN _
    | C.CAST _
    | C.GNU_BODY _
    -> (e,[])

and elimTernaryEE ee = 
    let resL = List.map elimTernaryE ee in
    let ee' = List.map fst resL in
    let vqL' = List.flatten (List.map snd resL) in
    (ee',vqL')

and extractVqL vqL loc =
  let vars = List.map fst vqL in
  let ss = List.map (fun (v,q) -> v |:=| (q,loc)) vqL in
  let (vars',ssIf',_) = elimTernarySS ss in
  (vars@vars',ssIf')

and elimTernaryS s : string list * C.statement list * C.statement list = 
  (* returns ([a;b],ssIf,s), whose meaning is *)
  (* int a,b; ssIf; s *)
  match s with
  | C.COMPUTATION(C.BINARY(C.ASSIGN,C.VARIABLE v,C.QUESTION(b,e1,e2)),loc) ->
     let (vars1,ssIf1,ss1) = elimTernaryS (v |:=| (e1,loc)) in
     let (vars2,ssIf2,ss2) = elimTernaryS (v |:=| (e2,loc)) in
     let vars = vars1 @ vars2 in
     let sIf = _IfSS b ss1 ss2 loc in
     let ssIf = ssIf1 @ ssIf2 @ [sIf] in
     (vars, ssIf, [_Nop])
  | C.COMPUTATION (e,loc) ->
     let (e',vqL') = elimTernaryE e in
     let (vars1,ssIf1) = extractVqL vqL' loc in
     let s' = C.COMPUTATION(e',loc) in     
     (vars1,ssIf1,[s'])
  | C.DEFINITION def ->
     let ss = elimTernaryDef def in
     ([],[],ss)
  | C.SEQUENCE(s1,s2,loc) ->
     let (vars1,ssIf1,ss1) = elimTernaryS s1 in
     let (vars2,ssIf2,ss2) = elimTernaryS s1 in
     let vars' = vars1 @ vars2 in
     let ssIf' = ssIf1 @ ssIf2 in
     let ss' = ss1 @ ss2 in
     (vars',ssIf',ss')
  | C.IF(e,s1,s2,loc) ->
     let (vars1,ssIf1,ss1) = elimTernaryS s1 in
     let (vars2,ssIf2,ss2) = elimTernaryS s1 in
     let vars' = vars1 @ vars2 in
     let ssIf' = ssIf1 @ ssIf2 in
     let s' = _IfSS e ss1 ss2 loc in
     (vars',ssIf',[s'])
  | C.WHILE(fml,e1,s1,loc) ->
     let (vars1,ssIf1,ss1) = elimTernaryS s1 in
     let s' = _WhileSS e1 ss1 loc in
     (vars1,ssIf1,[s'])
  | C.DOWHILE(fml,e1,s1,loc) -> 
     let (vars1,ssIf1,s1) = elimTernaryS s1 in
     let s' = _DoWhileSS e1 s1 loc in
     (vars1,ssIf1,[s'])
  | C.FOR(fml,fcls,e1,e2,s0,loc) ->
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _ForSS fcls e1 e2 ss0' loc in
     (vars',ssIf',[s'])
  | C.RETURN(e,loc) ->
     let (e',vqL') = elimTernaryE e in
     let (vars1,ssIf1) = extractVqL vqL' loc in
     let s' = C.RETURN(e',loc) in
     (vars1,ssIf1,[s'])
  | C.BLOCK(blk,loc) ->
     let blk' = eliminateTernaryB blk in
     let s' = C.BLOCK(blk',loc) in
     ([],[],[s'])
  | C.SWITCH(e,s0,loc) ->
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _SwitchSS e ss0' loc in
     (vars',ssIf',[s'])
  | C.CASE(e,s0,loc) -> 
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _CaseSS e ss0' loc in
     (vars',ssIf',[s'])
  | C.CASERANGE(e1,e2,s0,loc) -> 
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _CaseRangeSS e1 e2 ss0' loc in
     (vars',ssIf',[s'])
  | C.DEFAULT(s0,loc) -> 
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _DefaultSS ss0' loc in
     (vars',ssIf',[s'])
  | C.LABEL(name,s0,loc) ->
     let (vars',ssIf',ss0') = elimTernaryS s0 in
     let s' = _LabelSS name ss0' loc in
     (vars',ssIf',[s'])
  | C.NOP _
    | C.BREAK _
    | C.CONTINUE _
    | C.GOTO _
    | C.ASM _
    | C.COMPGOTO _
    | C.TRY_EXCEPT _ 
    | C.TRY_FINALLY _
    -> ([],[],[s])

and elimiminateTernaryS s =
  let (vars,ssIf,ss') = elimTernaryS s in
  let loc = getloc s in
  let ssDecl = List.map (fun v -> _VarDecl specInt v loc) vars in
  ssDecl @ ssIf @ ss'

and eliminateTernaryB blk =
  let ss = List.flatten (List.map elimiminateTernaryS blk.C.bstmts) in
  {
      C.blabels = blk.C.blabels;
      C.battrs = blk.C.battrs;
      C.bstmts = ss;
  }

and elimTernarySS ss =
    let resL = List.map elimTernaryS ss in
    let vars' = List.flatten (List.map (fun (x,_,_) -> x) resL) in
    let ssIf' = List.flatten (List.map (fun (_,y,_) -> y) resL) in
    let ss' = List.flatten (List.map (fun (_,_,z) -> z) resL) in
    let ss1' = List.filter (fun s -> s<>_Nop) ss' in
    let ss2' = if ss1' = [] then [_Nop] else ss1' in
    (vars',ssIf',ss2')

and elimTernaryDef def =
  (* 
returns ([x;y],ssIf,ssDef)
- int x = p?q:r + 1; becomes
  ([int x;a],[if(p){ a=q }else{ a=r }],[x = a+1])
- int x = y + 1; becomes 
  ([int x],[],[x = y+1])
*)
  match def with
  | C.FUNDEF(sname,blk,_,loc) ->
     let blk' = eliminateTernaryB blk in
     let s = C.DEFINITION (C.FUNDEF(sname,blk',loc,loc)) in
     [s]
  | C.DECDEF(init_name_gp,loc) ->
     let (spec, init_nameL) = init_name_gp in
     let mkDecl name init_exp =
       let init_name_gp' = (spec,[(name,init_exp)]) in
       let def' = C.DECDEF(init_name_gp',loc) in
       C.DEFINITION def'
     in
     let _ssDec = ref [] in
     let _ssIf = ref [] in
     let _ss = ref [] in
     for j = 0 to List.length init_nameL - 1 do
       let (namej,init_expj) = List.nth init_nameL j in
       let (v,_,_,_) = namej in
       match init_expj with
       | C.SINGLE_INIT exp ->
          let (e1,vqL1) = elimTernaryE exp in
          let (vars,ssIf) = extractVqL vqL1 loc in
          let sDec = mkDecl namej C.NO_INIT in
          let ssDec = List.map (fun v -> _VarDecl specInt v loc) vars in
          _ssDec := ssDec @ [sDec] @ !_ssDec;
          _ss := (v |:=| (e1,loc)) :: !_ss
       | _ ->
          _ssDec := (mkDecl namej init_expj) :: !_ssDec
     done;
     List.rev (!_ss @ !_ssIf @ !_ssDec)
  | C.ONLYTYPEDEF _
  | C.GLOBASM _
  | C.PRAGMA _ 
  | C.TYPEDEF _
  | C.S_FUNDEF _
  | C.S_INDDEF _
  | C.EXPRTRANSFORMER _
  | C.TRANSFORMER _
  | C.LINKAGE _
    -> 
     let s = C.DEFINITION def in
     [s]
;;    

let skipcondition s = noBreakControlReturn s || isLoopControl s
;;

(*-----------------*)
(*   New version   *)
(*-----------------*)
let rec transExpFW f_e f_s (e : C.expression) =
  match e with
  | C.QUESTION (e0,e1,e2) ->
     let (vva,ssa,ee') = transExpLFW f_e f_s [e0;e1;e2] in
     let e0a = List.nth ee' 0 in
     let e1a = List.nth ee' 1 in
     let e2a = List.nth ee' 2 in
     let (vvb,ssb,e') = f_e @@ C.QUESTION (e0a,e1a,e2a) in
     (vva @ vvb, ssa @ ssb, e')
  | C.UNARY(op,e0) ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.UNARY(op,e0a) in
     (vva @ vvb, ssa @ ssb, e')
  | C.BINARY(op,e0,e1) ->
     let (vva,ssa,ee') = transExpLFW f_e f_s [e0;e1] in
     let e0a = List.nth ee' 0 in
     let e1a = List.nth ee' 1 in
     let (vvb,ssb,e') = f_e @@ C.BINARY (op,e0a,e1a) in
     (vva @ vvb, ssa @ ssb, e')
  | C.CALL(e0,ee0) ->
     let (vva,ssa,ee') = transExpLFW f_e f_s (e0::ee0) in
     let e0a = List.hd ee' in
     let ee0a = List.tl ee' in
     let (vvb,ssb,e') = f_e @@ C.CALL(e0a,ee0a) in
     (vva @ vvb, ssa @ ssb, e')
  | C.COMMA ee ->
     let (vva,ssa,ee') = transExpLFW f_e f_s ee in
     let (vvb,ssb,e') = f_e @@ C.COMMA ee' in
     (vva @ vvb, ssa @ ssb, e')
  | C.PAREN e0 ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.PAREN e0a in
     (vva @ vvb, ssa @ ssb, e')
  | C.EXPR_SIZEOF e0 ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.EXPR_SIZEOF e0a in
     (vva @ vvb, ssa @ ssb, e')
  | C.EXPR_ALIGNOF e0 ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.EXPR_ALIGNOF e0a in
     (vva @ vvb, ssa @ ssb, e')
  | C.INDEX(e0,e1) ->
     let (vva,ssa,ee') = transExpLFW f_e f_s [e0;e1] in
     let e0a = List.nth ee' 0 in
     let e1a = List.nth ee' 1 in
     let (vvb,ssb,e') = f_e @@ C.INDEX (e0a,e1a) in
     (vva @ vvb, ssa @ ssb, e')
  | C.MEMBEROF(e0,str) ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.MEMBEROF(e0a,str) in
     (vva @ vvb, ssa @ ssb, e')
  | C.MEMBEROFPTR(e0,str) ->
     let (vva,ssa,e0a) = transExpFW f_e f_s e0 in
     let (vvb,ssb,e') = f_e @@ C.MEMBEROFPTR(e0a,str) in
     (vva @ vvb, ssa @ ssb, e')
  | C.NOTHING -> ([], [], e)
  | C.LABELADDR _ -> ([], [], e)
  | C.CONSTANT _ -> ([], [], e)
  | C.VARIABLE _ -> ([], [], e)
  | C.EXPR_PATTERN _ -> ([], [], e)
  | C.GNU_BODY b ->
     let b' = transBlkFW f_e f_s b in
     let (vv,ss,e') = f_e @@ C.GNU_BODY b' in
     (vv,ss,e')
  | C.TYPE_ALIGNOF (spec,decl) ->
     let (vva,ssa,decl') = transDeclFW f_e f_s decl in
     let (vvb,ssb,e') = f_e @@ C.TYPE_ALIGNOF (spec,decl') in
     (vva @ vvb, ssa @ ssb,e')
  | C.TYPE_SIZEOF (spec,decl) -> 
     let (vva,ssa,decl') = transDeclFW f_e f_s decl in
     let (vvb,ssb,e') = f_e @@ C.TYPE_SIZEOF (spec,decl') in
     (vva @ vvb, ssa @ ssb,e')
  | C.CAST ((spec,decl), iexp) ->
     let (vva,ssa,decl') = transDeclFW f_e f_s decl in
     let (vvb,ssb,iexp') = transIexpFW f_e f_s iexp in
     let (vvc,ssc,e') = f_e @@ C.CAST ((spec,decl'),iexp') in
     (vva @ vvb @ vvc, ssa @ ssb @ ssc,e')
     
and transExpLFW f_e f_s ee =
  let vseL = List.map (transExpFW f_e f_s) ee in
  let vv' = List.flatten @@ List.map (fun (vv,_,_) -> vv) vseL in
  let ss' = List.flatten @@ List.map (fun (_,ss,_) -> ss) vseL in
  let ee' = List.map (fun (_,_,e) -> e) vseL in
  (vv',ss',ee')

and transStmtFW f_e f_s s =
  match s with
 | C.NOP _ -> ([], [s])
 | C.COMPUTATION (e,loc) ->
    let (vva,ssa,e') = transExpFW f_e f_s e in
    let (vvb,ssb) = f_s @@ C.COMPUTATION (e',loc) in
    (vva @ vvb, ssa @ ssb)
 | C.BLOCK (b,loc) ->
    let b' = transBlkFW f_e f_s b in
    let (vvb,ssb) = f_s @@ C.BLOCK (b',loc) in
    (vvb,ssb)
 | C.SEQUENCE (s0,s1,loc) ->
    let (vv0,ss0) = transStmtFW f_e f_s s0 in
    let (vv1,ss1) = transStmtFW f_e f_s s1 in
    (vv0 @ vv1, ss0 @ ss1)
 | C.IF (eCond,sThen,sElse,loc) ->
    let (vvCond,ssCond,eCond') = transExpFW f_e f_s eCond in
    let sThen' = ss2stmt @@ transStmtCloseFW f_e f_s sThen in
    let sElse' = ss2stmt @@ transStmtCloseFW f_e f_s sElse in
    let (vvb,ssb) = f_s @@ C.IF (eCond',sThen',sElse',loc) in
    (vvCond @ vvb, ssCond @ ssb)
 | C.WHILE (fml,eCond,sBody,loc) ->
    let (vvCond,ssCond,eCond') = transExpFW f_e f_s eCond in
    inclLoopDepth ();
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    declLoopDepth ();
    let sBody' = ss2stmt (ssBody' @ ssCond) in
    let (vvb,ssb) = f_s @@ C.WHILE (fml,eCond',sBody',loc) in
    (vvb @ vvCond, ssCond @ ssb)
 | C.DOWHILE (fml,eCond,sBody,loc) -> 
    let (vvCond,ssCond,eCond') = transExpFW f_e f_s eCond in
    inclLoopDepth ();
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    declLoopDepth ();
    let sBody' = ss2stmt (ssBody' @ ssCond) in
    let (vvb,ssb) = f_s @@ C.DOWHILE (fml,eCond',sBody',loc) in
    (vvb @ vvCond, ssCond @ ssb)
 | C.FOR (fml, fcls, e0, e1, sBody, loc) ->
    let (vv0,ss0,e0') = transExpFW f_e f_s e0 in
    let (vv1,ss1,e1') = transExpFW f_e f_s e1 in
    inclLoopDepth ();
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    declLoopDepth ();
    let sBody' = ss2stmt (ssBody' @ ss0 @ ss1) in
    let (vvb,ssb) = f_s @@ C.FOR (fml,fcls,e0',e1',sBody',loc) in
    (vvb @ vv0 @ vv1, ss0 @ ss1 @ ssb)
 | C.BREAK _ ->
    let (vvb,ssb) = f_s s in
    (vvb, ssb)
 | C.CONTINUE _ ->
    let (vvb,ssb) = f_s s in
    (vvb, ssb)
 | C.RETURN (e,loc) ->
    let (vv,ss,e') = transExpFW f_e f_s e in
    let (vvb,ssb) = f_s @@ C.RETURN(e',loc) in
    (vvb @ vv,ss @ ssb)
 | C.SWITCH (eCond, sBody, loc) ->
    let (vvCond,ssCond,eCond') = transExpFW f_e f_s eCond in
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    let sBody' = ss2stmt ssBody' in
    let (vvb,ssb) = f_s @@ C.SWITCH (eCond', sBody', loc) in
    (vvb @ vvCond,ssCond @ ssb)
 | C.CASE (e,sBody,loc) ->
    let (vvCond,ssCond,e') = transExpFW f_e f_s e in
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    let sBody' = ss2stmt ssBody' in
    let (vvb,ssb) = f_s @@ C.CASE (e', sBody', loc) in
    (vvb @ vvCond,ssCond @ ssb)
 | C.CASERANGE (e0,e1,sBody,loc) ->
    let (vv0,ss0,e0') = transExpFW f_e f_s e0 in
    let (vv1,ss1,e1') = transExpFW f_e f_s e1 in
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    let sBody' = ss2stmt ssBody' in
    let (vvb,ssb) = f_s @@ C.CASERANGE (e0', e1', sBody', loc) in
    (vvb @ vv0 @ vv1, ss0 @ ss1 @ ssb)
 | C.DEFAULT (sBody,loc) ->
    let ssBody' = transStmtCloseFW f_e f_s sBody in
    let sBody' = ss2stmt ssBody' in
    let (vvb,ssb) = f_s @@ C.DEFAULT (sBody', loc) in
    (vvb, ssb)
 | C.LABEL (str,s,loc) ->
    let ss' = transStmtCloseFW f_e f_s s in
    let s' = ss2stmt ss' in
    let (vvb,ssb) = f_s @@ C.LABEL (str,s',loc) in
    (vvb, ssb)
 | C.GOTO _ -> 
    let (vvb,ssb) = f_s s in
    (vvb, ssb)
 | C.COMPGOTO (e,loc) ->
    let (vv0,ss0,e') = transExpFW f_e f_s e in
    let (vvb,ssb) = f_s @@ C.COMPGOTO(e',loc) in
    (vvb @ vv0,ss0 @ ssb)
 | C.DEFINITION def ->
    let def' = transDefFW f_e f_s def in
    let (vvb,ssb) = f_s @@ C.DEFINITION def' in
    (vvb, ssb)
 | C.ASM _ -> (* dummy *)
    let (vvb,ssb) = f_s s in
    (vvb, ssb)
 | C.TRY_EXCEPT (b0,e,b1,loc) ->
    let (vv0,ss0,e') = transExpFW f_e f_s e in
    let b0' = transBlkFW f_e f_s b0 in
    let b1' = transBlkFW f_e f_s b1 in
    let (vvb,ssb) = f_s @@ C.TRY_EXCEPT (b0',e',b1',loc) in
    (vvb @ vv0,ss0 @ ssb)
 | C.TRY_FINALLY (b0,b1,loc) ->
    let b0' = transBlkFW f_e f_s b0 in
    let b1' = transBlkFW f_e f_s b1 in
    let (vvb,ssb) = f_s @@ C.TRY_FINALLY (b0',b1',loc) in
    (vvb, ssb)

and transBlkFW f_e f_s b =
  let ss = b.C.bstmts in
  let ss' = List.flatten @@ List.map (transStmtCloseFW f_e f_s) ss in
  { C.blabels = b.C.blabels; C.battrs = b.C.battrs; C.bstmts = ss' }

and transStmtCloseFW f_e f_s s =
  let (vv,ss) = transStmtFW f_e f_s s in
  let loc = getloc s in
  let ssDecl = List.map (fun v -> _VarDecl specInt v loc) vv in
  ssDecl @ ss
  
and transIexpFW f_e f_s iexp =                  
  match iexp with
  | C.NO_INIT -> ([],[],C.NO_INIT)
  | C.SINGLE_INIT e ->
     let (vv,ss,e') = transExpFW f_e f_s e in
     let ie' = C.SINGLE_INIT e' in
     (vv,ss,ie')
  | C.COMPOUND_INIT weL ->
     let f we =
       let (iw,ie) = we in
       let (vv,ss,ie') = transIexpFW f_e f_s ie in
       let we' = (iw,ie') in
       (vv,ss,we')
     in
     let vswL = List.map f weL in
     let vva = List.flatten @@ List.map (fun (vv,_,_) -> vv) vswL in
     let ssa = List.flatten @@ List.map (fun (_,ss,_) -> ss) vswL in
     let weL' = List.map (fun (_,_,we) -> we) vswL in
     let ie' = C.COMPOUND_INIT weL' in
     (vva, ssa, ie')
     
and transDeclFW f_e f_s decl = ([],[],decl) (* dummy *)
                             
and transDefFW f_e f_s def : C.definition =  
  match def with    
  | C.FUNDEF (singlename,blk,cloc1,cloc2) ->     
     let blk' = transBlkFW f_e f_s blk in     
     C.FUNDEF (singlename,blk',cloc1,cloc2)     
  | C.S_FUNDEF (fml1,fml2,def1,cloc) ->     
     let def1' = transDefFW f_e f_s def1 in     
     C.S_FUNDEF (fml1,fml2,def1',cloc)     
  | C.S_INDDEF (indclsL,cloc) -> def (* dummy *) 
  | C.DECDEF (initname_gp,cloc) -> def (* dummy *)     
  | C.TYPEDEF (namegp,cloc) -> def (* dummy *)                             
  | C.ONLYTYPEDEF (spec,cloc) -> def (* dummy *) 
  | C.GLOBASM (_,_) -> def (* dummy *)                     
  | C.PRAGMA (_,_) -> def (* dummy *)                    
  | C.LINKAGE (str,cloc,defL) ->     
     let defL' = List.map (transDefFW f_e f_s) defL in     
     C.LINKAGE (str,cloc,defL')     
  | C.TRANSFORMER (def1,defL,cloc) ->     
     let def1' = transDefFW f_e f_s def1 in     
     let defL' = List.map (transDefFW f_e f_s) defL in     
     C.TRANSFORMER (def1',defL',cloc)     
  | C.EXPRTRANSFORMER (e0,e1,cloc) -> def (* dummy *)
;;                 


(* identity transformer function *)
let f_e_init e = ([],[],e);;
let f_s_init s = ([],[s]);; 

(* transformer function (with faisal's function) *)
let f_s_trans_extract (s : C.statement) =
  let ss1 = VcpExtract.extract_statements [s] in
  ([],ss1)
;;

(* transformer function (original) *)
let f_s_trans s =
  match s with
  | C.FOR (_,forCls,eCond,eDiff,sBody,loc) ->
     (*
     (* Local-declaration lifting *)
     let _ssDecl = ref [] in
     let sBody1 = decompDI_statement _ssDecl sBody in
      *)
     (* Do transformation *)
     let (sHead,aaWhile) = transForCore forCls eCond eDiff sBody loc in
     let ssWhile = AA.toSS aaWhile in
     let ssWhile1 = sHead :: ssWhile in
     ([],ssWhile1)
       (*
     begin
       match !_ssDecl with
       | [] -> ([],ssWhile1)
       | _ ->
          (* Make nested block for lifted local variable declarations *)
          let blk_inner =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = ssWhile1;
            }
          in
          let blk_outer =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
            }
          in
          ([],[C.BLOCK(blk_outer,loc)])
     end     
        *)
  | _ when skipcondition s -> ([],[s])
  | C.WHILE (fml,eCond,sBody,loc) ->
     (*
     (* Local-declaration lifting *)
     let _ssDecl = ref [] in
     let sBody1 = decompDI_statement _ssDecl sBody in
      *)
     (* Do transformation *)
     let aaBody = AA.fromStmt sBody in
     let aaWhile = transWhileCore false eCond aaBody loc in
     let ssWhile = AA.toSS aaWhile in
     ([],ssWhile)
       (*
     begin
       match !_ssDecl with
       | [] -> ([],ssWhile)             
       | _ ->
          (* Make nested block for lifted local variable declarations *)
          let blk_inner =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = ssWhile;
            }
          in
          let blk_outer =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
            }
          in
          ([],[C.BLOCK(blk_outer,loc)])
     end
        *)
  | C.IF(eCond,sThen,sElse,loc) -> 
     let aaThen = AA.fromStmt sThen in
     let aaElse = AA.fromStmt sElse in
     let aaIf = transIfCore eCond aaThen aaElse loc in
     ([], AA.toSS aaIf)
  | C.DOWHILE(_,eCond,sBody,loc) ->
     (*
     (* Local-declaration lifting *)
     let _ssDecl = ref [] in
     let sBody1 = decompDI_statement _ssDecl sBody in
      *)
     (* Do transformation *)
     let aaBody = AA.fromStmt sBody in
     let aaDoWhile = transDoWhileCore eCond aaBody loc in
     let ssDoWhile = AA.toSS aaDoWhile in
     ([],ssDoWhile)
     (*
     begin
       match !_ssDecl with
       | [] -> ([],ssDoWhile)             
       | _ ->
          (* Make nested block for lifted local variable declarations *)
          let blk_inner =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = ssDoWhile;
            }
          in
          let blk_outer =
            {
              C.blabels = [];
              C.battrs = [];
              C.bstmts = (List.rev !_ssDecl) @ [C.BLOCK (blk_inner,loc)];
            }
          in
          ([],[C.BLOCK(blk_outer,loc)])
     end
      *)
  | C.SWITCH (eCond,sBody,loc) ->
     let ssBody = SS.fromStmt sBody in
     let aaSwitch = transSwitchCore eCond ssBody loc in
     ([], AA.toSS aaSwitch)
  | _ -> ([],[s])
;;


(* Call this in SLAC *)
let transBlock f_e f_s blk =
  let stmtL = blk.C.bstmts in
  let stmtL' = List.map rename_liftdecl_loop stmtL in
  doIfDebug print_endline "========";
  doIfDebug print_endline "Local Variable Renaming + Declaration Lifting";
  doIfDebug print_endline "========";
  doIfDebug flush_all ();
  doIfDebug (List.iter print_statement) stmtL';
  {
    C.blabels = blk.C.blabels;
    C.battrs = blk.C.battrs;
    C.bstmts = List.flatten (List.map (transStmtCloseFW f_e f_s) stmtL');
  }
;;    

let rec transDefinition f_e f_s def =
  match def with    
  | C.FUNDEF (singlename,blk,cloc1,cloc2) ->
     let blk' = transBlock f_e f_s blk in
     C.FUNDEF (singlename,blk',cloc1,cloc2)     
  | C.S_FUNDEF (fml1,fml2,def1,cloc) ->     
     let def1' = transDefinition f_e f_s def1 in     
     C.S_FUNDEF (fml1,fml2,def1',cloc)     
  | C.LINKAGE (str,cloc,defL) ->     
     let defL' = List.map (transDefinition f_e f_s) defL in     
     C.LINKAGE (str,cloc,defL')     
  | C.TRANSFORMER (def1,defL,cloc) ->     
     let def1' = transDefinition f_e f_s def1 in     
     let defL' = List.map (transDefinition f_e f_s) defL in     
     C.TRANSFORMER (def1',defL',cloc)     
  | _ -> def
;;                 



let transform_file2 (f : C.file) : C.file =
  let f_e = f_e_init in
  let (fname,deflist) = f in
  doIfDebug print_endline "=======================";
  doIfDebug print_endline "Original Input";
  doIfDebug print_endline "=======================";
  doIfDebug printFile f;
    
  let deflist1 = List.map (transDefinition f_e f_s_trans) deflist in
  doIfDebug print_endline "=======================";
  doIfDebug print_endline "Transformation Result";
  doIfDebug print_endline "=======================";
  doIfDebug printFile (fname,deflist1);  
  (fname,deflist1)
;;

