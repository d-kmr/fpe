open Tools;;
open Smtsyntax;;
open Z3;;

module C = Command;;
module ZA = Z3.Arithmetic;;
module ZI = Z3.Arithmetic.Integer;;
module ZB = Z3.Boolean;;
module ZE = Z3.Expr;;
module ZQ = Z3.Quantifier;;
module ZSym = Z3.Symbol;;


module EnrichedContext = struct 
  type t =
    context *
      (Smtsyntax.Sort.t * Sort.sort) list * 
      (string * Symbol.symbol * FuncDecl.func_decl * int option) list
  (* an enriched context has the form (ctx,sort_info,func_info) *)
  (* sort_info is an assoc list of smt-sort and z3-sort		*)
  (* e.g., [(Int,<int>) ; (Bool,<bool>) ; ..]			*)
  (* func_info is an assoc list of (name,symbol,fdecl,db_id)	*)
  (* 'db_id' is the de-bruijn index of the variable 		*)
  (* 'x' is replaced by 'n' if ('x',..,Some 'n') is in ectx	*)
      
  let init ctx : t =
    let myint = Smtsyntax.Sort.Name "Int" in
    let mybool = Smtsyntax.Sort.Name "Bool" in
    let ints = Arithmetic.Integer.mk_sort ctx in
    let bools = Boolean.mk_sort ctx in
    (ctx,[(myint,ints);(mybool,bools)],[])

  let lookupFun (ectx : t) name = 
    let (_,_,fdata) = ectx in
    let fdata' = List.map (fun (a,b,c,d) -> (a,(b,c,d))) fdata in
    List.assoc name fdata'

  exception LookupSortError of string
    
  let rec lookupSort (ectx : t) sort =
    let module SS = Smtsyntax.Sort in
    let (cxt,sdata,_) = ectx in
    let sortmatch sort1 sort2 =
      match sort1,sort2 with
      | SS.Name p1,SS.Name p2 -> 
	if p1 = p2 then true else false
      | SS.App(p1,_),SS.App(p2,_) ->
	if p1 = p2 then true else false
      | _,_ -> false
    in
    let msorts = List.filter (fun (s,_)-> sortmatch s sort) sdata in
    if msorts = [] then raise (LookupSortError (SS.to_string sort))
    else
      (fun (_,z)->z) (List.hd msorts)

  let get_range (ectx : t) name =
    let (_,fdecl,_) = lookupFun ectx name in
    FuncDecl.get_range fdecl

  let isDeclaredFun (ectx : t) name =
    try
      let _ = lookupFun ectx name in true
    with Not_found -> false

  let get_int (ectx : t) = 
    let myint = Smtsyntax.Sort.Name "Int" in
    lookupSort ectx myint

  let get_bool (ectx : t) =
    let mybool = Smtsyntax.Sort.Name "Bool" in
    lookupSort ectx mybool

  (* add constants of given sort *)
  let add_consts (ectx : t) sort names : t = 
    let (ctx,sdata,fdata) = ectx in
    let syms = List.map (Z3.Symbol.mk_string ctx) names in
    let fdecls = List.map 
      (fun s -> Z3.FuncDecl.mk_const_decl ctx s sort)
      syms
    in
    let itemLst = zipLst names (zipLst syms fdecls) in
    let fdata1 = List.map (fun (x,(y,z)) -> (x,y,z,None)) itemLst in
    (ctx,sdata,fdata1@fdata)

  (* add int constants *)
  let add_iconsts (ectx : t) names =
    let ints = get_int ectx in 
    add_consts ectx ints names

  (* add bool constants *)
  let add_bconsts (ectx : t) names = 
    let bools = get_bool ectx in 
    add_consts ectx bools names

  let add_fun (ectx : t) f sorts sort : t = 
    let (ctx,sdata,fdata) = ectx in
    let sym = Z3.Symbol.mk_string ctx f in
    let fdecl = Z3.FuncDecl.mk_func_decl ctx sym sorts sort in
    let fdat = (f,sym,fdecl,None) in
    (ctx,sdata,fdat::fdata)

  let shift_index (ectx : t) : t =
    let (ctx,sdata,fdata) = ectx in
    let shift_id opt = match opt with
      | None -> None
      | Some n -> Some (n+1)
    in
    let shift_finfo (f,s,d,o) = (f,s,d,shift_id o) in
    (ctx, sdata, List.map shift_finfo fdata)
      
  let add_bvar (ectx : t) v sort : t =
    let (ctx,sdata,fdata) = shift_index ectx in
    let sym = Z3.Symbol.mk_string ctx v in
    let fdecl = Z3.FuncDecl.mk_func_decl ctx sym [] sort in
    let fdat = (v,sym,fdecl,Some 0) in
    (ctx,sdata,fdat::fdata)    

  let get_consts (ectx : t) =
    let module ZF = Z3.FuncDecl in
    let (_,_,fdata) = ectx in
    let isConst fdecl =
      if ZF.get_domain fdecl = [] then true else false
    in
    let xl = List.filter (fun (_,_,fdecl,_) -> isConst fdecl) fdata in
    let xdl = List.rev (List.map (fun (x,_,fdecl,_) -> (x,fdecl)) xl) in
    List.map (fun (x,fd) -> (x,ZF.get_range fd)) xdl
      
end
;;

module EC = EnrichedContext;;

let make_app (ectx : EC.t) f exps =
  let (ctx,_,_) = ectx in
  match f with
  | "+" -> ZA.mk_add ctx exps
  | "*" -> ZA.mk_mul ctx exps
  | "-" ->
    if List.length exps = 1 then
      ZA.mk_unary_minus ctx (List.hd exps)
    else ZA.mk_sub ctx exps
  | "div" -> ZA.mk_div ctx (List.nth exps 0) (List.nth exps 1)
  | "/" -> ZA.mk_div ctx (List.nth exps 0) (List.nth exps 1)  (* it also receives "/" *)
  | "mod" -> ZI.mk_mod ctx (List.nth exps 0) (List.nth exps 1)
  | "<" -> ZA.mk_lt ctx (List.nth exps 0) (List.nth exps 1)
  | ">" -> ZA.mk_gt ctx (List.nth exps 0) (List.nth exps 1)
  | "<=" -> ZA.mk_le ctx (List.nth exps 0) (List.nth exps 1)
  | ">=" -> ZA.mk_ge ctx (List.nth exps 0) (List.nth exps 1)
  | "=" -> ZB.mk_eq ctx (List.nth exps 0) (List.nth exps 1)
  | "distinct" -> ZB.mk_distinct ctx exps
  | "not" -> ZB.mk_not ctx (List.hd exps)
  | "and" -> ZB.mk_and ctx exps
  | "or" -> ZB.mk_or ctx exps
  | "ite" -> ZB.mk_ite ctx (List.nth exps 0) (List.nth exps 1) (List.nth exps 2)
  | "iff" -> ZB.mk_iff ctx (List.nth exps 0) (List.nth exps 1)
  | "xor" -> ZB.mk_xor ctx (List.nth exps 0) (List.nth exps 1)
  | "imp" -> ZB.mk_implies ctx (List.nth exps 0) (List.nth exps 1)
  | _ ->
     let (_,fdecl,_) = EC.lookupFun ectx f in
     Expr.mk_app ctx fdecl exps
;;

(* translation of expressions *) (** Error here *)
let rec transExpr (ectx : EC.t) exp =
  let (ctx,_,_) = ectx in
  let module SE = Exp in
  let ints = EC.get_int ectx in
  match exp with
  | SE.Int n -> ZE.mk_numeral_int ctx n ints
  | SE.Var v ->
    let (_,vdecl,opt) = EC.lookupFun ectx v in
    begin
      match opt with
      | None -> ZE.mk_const_f ctx vdecl
      | Some id -> ZQ.mk_bound ctx id (EC.get_range ectx v)
    end
  | SE.App(f,args) ->
    let args' = List.map (transExpr ectx) args in
    make_app ectx f args'
  | SE.Let(_,_) -> ZE.mk_const_s ctx "Let" ints		(* dummy *)
  | SE.Att(exp,_) -> transExpr ectx exp			(* dummy *)
  | SE.All (vss,body) -> 
    let vars = List.map (fun (v,_) -> v) vss in
    let sorts = List.map (fun (_,s) -> s) vss in
    let sorts' = List.map (EC.lookupSort ectx) sorts in
    let names = List.map (fun x -> ZSym.mk_string ctx x) vars in
    let ectxp = ref ectx in
    let vss = zipLst vars sorts' in
    List.iter
      (fun (x,s) -> ectxp := EC.add_bvar !ectxp x s)
      vss;
    let body1 = transExpr !ectxp body in
    let qexp =
      ZQ.mk_forall ctx
	sorts'
	names
	body1		(* main part *)
	None [] [] None None		(* auxiliary part *)
    in ZQ.expr_of_quantifier qexp
  | SE.Ex (vss,body) ->
    let vars = List.map (fun (v,_) -> v) vss in
    let sorts = List.map (fun (_,s) -> s) vss in
    let sorts' = List.map (EC.lookupSort ectx) sorts in
    let names = List.map (fun x -> ZSym.mk_string ctx x) vars in
    let ectxp = ref ectx in
    let vss = zipLst vars sorts' in
    List.iter
      (fun (x,s) -> ectxp := EC.add_bvar !ectxp x s)
      vss;
    let body1 = transExpr !ectxp body in
    let qexp =
      ZQ.mk_exists ctx
	sorts'
	names
	body1		(* main part *)
	None [] [] None None		(* auxiliary part *)
    in ZQ.expr_of_quantifier qexp
  
;;

(* Translation of datatypes				*)
(* mk_z3constructor ctx dtps i j 			*)
(* It makes Z3-constructor of the j-th constructor of	*)
(* the i-th type of the datatype dtps			*)
let mk_z3constructor
    (ectx : EC.t)
    (dtps : C.datatype list) i j =
  let module EC = EnrichedContext in
  let (ctx,_,_) = ectx in
  let get_body_nthtype i = (fun (_,y)->y) (List.nth dtps i) in
  let get_nthbody_nthtype i j =
    List.nth (get_body_nthtype i) j in
  let get_cons_nthbody_nthtype i j =
    (fun (x,_) -> x) (get_nthbody_nthtype i j) in
  let get_adecs_nthbody_nthtype i j =
    (fun (_,y) -> y) (get_nthbody_nthtype i j) in
  let adecslen_nthbody_nthtype i j =
    List.length (get_adecs_nthbody_nthtype i j) in
  let get_nthadec_nthbody_nthtype i j k =
    List.nth (get_adecs_nthbody_nthtype i j) k in
  let get_acc_nthadec_nthabody_nthtype i j k =
    (fun (x,_) -> x) (get_nthadec_nthbody_nthtype i j k) in
  let get_accsort_nthadec_nthabody_nthtype i j k = 
    (fun (_,y) -> y) (get_nthadec_nthbody_nthtype i j k) in
  let cons = get_cons_nthbody_nthtype i j in
  let iscons = "is_"^cons in
  let sym_iscons = Z3.Symbol.mk_string ctx iscons in
  let alst = List.rev (genLst (adecslen_nthbody_nthtype i j)) in
  let accs = List.map (get_acc_nthadec_nthabody_nthtype i j) alst in
  let sym_accs = List.map (Z3.Symbol.mk_string ctx) accs in
  let asorts = List.map (get_accsort_nthadec_nthabody_nthtype i j) alst in
  let asorts' = List.map (EC.lookupSort ectx) asorts in
  let asorts_opt = List.map (fun x -> Some x) asorts' in
  let ilst = List.map (fun _ -> 1) alst in	
  Z3.Datatype.mk_constructor_s
    ctx
    cons		(* Name of the constructor <cons> *)
    sym_iscons		(* Symbol of the recognizer "is_<cons>" *)
    sym_accs		(* Symbols of the accessors *)
    asorts_opt		(* Sorts of the accessors *)
    ilst		(* I'm not sure the role of this list *)
;;

let mk_z3constructors ectx dtps i =
  let get_body_nthtype i = (fun (_,y)->y) (List.nth dtps i) in
  let bodylen_nthtype i = List.length (get_body_nthtype i) in
  let blst = List.rev (genLst (bodylen_nthtype i)) in
  List.map (mk_z3constructor ectx dtps i) blst
;;

(* mk_econtext coms					*)
(* It creates an ectx from given commands		*)
(* It checks DecFn, DecSt, 				*)
(* DefFn (if it's not decl'd), and DecDT		*)
(* Other commands are skipped				*)
(* DecVar,DecCons,DecFns,DecPreds,DefSt,DefFn are skipped *)
(* since they are already eliminated			*)
let mk_econtext ~modelflag ~ucflag commands : EC.t =
  let module SS = Smtsyntax.Sort in
  let module ZS = Z3.Sort in
  let module ZD = Z3.Datatype in
  let _ctxSeed = ref [] in
  if modelflag then _ctxSeed := ("model","true") :: !_ctxSeed else ();
  if ucflag then _ctxSeed := ("unsat_core","true") :: !_ctxSeed else ();
  let ctx = Z3.mk_context !_ctxSeed in
  let ectx = ref (EC.init ctx) in
  let rec mk_ectx coms =
    if coms = [] then () else
    let hdcom = List.hd coms in
    let tlcom = List.tl coms in
    match hdcom with
    | C.DecFn(f,sorts,sort) ->
      let sorts' = List.map (EC.lookupSort !ectx) sorts in
      let sort' = EC.lookupSort !ectx sort in
      ectx := EC.add_fun !ectx f sorts' sort';
     mk_ectx tlcom
    | C.DecSt(name,_) ->
      let (ctx,sdata,fdata) = !ectx in
      let sort = SS.Name name in
      let sort' = ZS.mk_uninterpreted_s ctx name in
      ectx := (ctx,(sort,sort')::sdata,fdata);
      mk_ectx tlcom
    | C.DecDT(vars,dtps) ->
      let (ctx,sdata,fdata) = !ectx in
      let prmsort_smt = List.map (fun v -> SS.Name v) vars in
      let prmsort_z3 = List.map (ZS.mk_uninterpreted_s ctx) vars in
      let ectx1 = (ctx,(zipLst prmsort_smt prmsort_z3)@sdata,fdata) in
      let n = List.length dtps in
      let nlst = List.rev (genLst n) in
      let get_name_nthtype i = (fun (x,_)->x) (List.nth dtps i) in
      let typenames = List.map get_name_nthtype nlst in
      let typename0 = List.nth typenames 0 in
      let nthConstructors i = mk_z3constructors ectx1 dtps i in
      let constructors0 = nthConstructors 0 in
      let z3Sort = ZD.mk_sort_s ctx typename0 constructors0 in
      let smtSort =
	if vars = [] then SS.Name typename0
	else
	  let argsorts = List.map (fun v -> SS.Name v) vars in
	  SS.App(typename0,argsorts)
      in
      ectx := (ctx,(smtSort, z3Sort)::sdata,fdata);
      mk_ectx tlcom
    | _ -> mk_ectx tlcom
  in
  mk_ectx commands;
  !ectx
;;

module SimpleExp = struct
  type t = Cons of string | Int of Bignum.t | OTHER
  (* Bignum is used for too big numbers *)

  let of_exp e : t =
    let strexp = ZE.to_string e in
    let local_bignum_of_string s =
      try
	    Bignum.of_string s
      with
	    Failure _ -> (* the case of minus integer, like (- 1) *)
        let s' = Bytes.sub s 2 (Bytes.length s - 4) in (* eliminate parenthese *)
        Bignum.of_string s'
    in
    if ZE.is_numeral e
    then
      let bn = local_bignum_of_string strexp in
   	  Int bn
    else
      if ZE.is_const e
      then Cons strexp
      else OTHER

  let to_bignum e : Bignum.t =
	match e with
	| Int bn -> bn
	| _ -> Bignum.of_int (-1)

  let optexp_to_bignum oe =
	match oe with
	| None -> Bignum.of_int (-1)
	| Some e -> to_bignum (of_exp e)
	  
  let of_optexp oe =
    match oe with
    | None -> OTHER
    | Some e -> of_exp e

  let to_string (se : t) =
    match se with
    | Cons str -> str
    | Int bn -> Bignum.to_string bn
    | OTHER -> "OTHER"
    
end
;;

module SatcheckResult = struct
  type t = 
    |  Model of (bytes * Bignum.t) list (* model [(x,1);(y,2)] when sat *)
    | UnsatCore of Z3.Expr.expr list (* unsat-core [e1;e2] when unsat *)
    | Unknown

end
;;
open SatcheckResult
;;

let checkCommands ~modelflag ~ucflag vars commands : SatcheckResult.t =
  let ectx0 = mk_econtext modelflag ucflag commands in
  let ectx = EC.add_iconsts ectx0 vars in
  let (ctx,sdata,fdata) = ectx in
  let t_qe = Tactic.mk_tactic ctx "qe" in
  let t_smt = Tactic.mk_tactic ctx "smt" in
  let tactic = Tactic.and_then ctx t_qe t_smt [] in
  let solver = Solver.mk_solver_t ctx tactic in
  let _expL = ref [] in
  let rec mk_mysolver com =
    if com = [] then ()
    else
      let hdcom = List.hd com in
      let tlcom = List.tl com in
      match hdcom with
      | C.DecVar(_,_)
      | C.DecCons(_,_)
      | C.DecFns _
      | C.DecSt(_,_)
      | C.DecPreds _
      | C.DefSt(_,_,_)
      | C.DefFn(_,_,_,_)
	(* skipped since already eliminated in preproccessing *)
      | C.DecFn(_,_,_)
      |	C.DecDT(_,_)
	(* skipped since already treated in mk_econtext *)
      | C.Push _
      | C.Pop _
      | C.GetAss
      | C.GetPrf
      | C.GetUnsat
      | C.GetAsgn
      | C.SetOpt(_,_)
      | C.GetInfo _
      | C.SetInfo(_,_)
      | C.Exit
      | C.Echo _
      | C.GetModel
      | C.Reset
      | C.Display _
      | C.Simpfy(_,_)
      | C.Eval(_,_)
      | C.Model
      | C.GetOpt _ -> 
	(* ignored since they are out of scope *)
	       mk_mysolver tlcom
      | C.Ass exp ->
         let exp' = try transExpr ectx exp  with x -> raise x in
         Solver.assert_and_track solver exp' exp';
	     mk_mysolver tlcom
      | C.CheckSat -> ()	(* finishes if check-sat comes *)
      | C.GetVal exp -> mk_mysolver tlcom (* dummy *)
  in
  mk_mysolver commands;
  Ftools.pf_s "Z3" (fun x -> print_endline (Solver.to_string x)) solver;
  
  match Solver.check solver [],modelflag,ucflag with
  | Z3.Solver.SATISFIABLE,true,_ ->
     begin
       match Solver.get_model solver with
       | None -> Model []		(* Dummy *)
       | Some model ->
	      let evalexp e = Z3.Model.evaluate model e false in
	      let evalcons (v,s) = evalexp (ZE.mk_const_s ctx v s) in
	      let varsorts = EC.get_consts ectx in
	      let vars = List.map (fun (x,_)->x) varsorts in
	      let optvals = List.map evalcons varsorts in
	      let valbnL = List.map SimpleExp.optexp_to_bignum optvals in
	      let varvalbnL = zipLst vars valbnL in
          (* List.iter (fun (v,bn) -> print_endline (v ^ "=" ^ (Bignum.to_string bn))) varvalbnL; *)
	      Model varvalbnL
            (*	(true, [model])*)
     end
  | Z3.Solver.SATISFIABLE,false,_ ->
     Model []
  | Z3.Solver.UNSATISFIABLE,_,true ->
     let uc = Solver.get_unsat_core solver in
     UnsatCore uc
  | Z3.Solver.UNSATISFIABLE,_,false ->
     UnsatCore []
  | Z3.Solver.UNKNOWN,_,_ ->
     Unknown
;;

(* for avoiding the Z3 bug *)
let checkExp_FIX ~modelflag ~ucflag exp =
  let myint = Smtsyntax.Sort.Name "Int" in
  let vars = Exp.fv exp in
  let cDecls = List.map (fun v -> C.DecVar (v,myint)) vars in
  let eMin = Exp.Int (-1000000) in
  let cLimits = List.map (fun v -> C.Ass (Exp.App("<",[eMin;Exp.Var v]))) vars in  
  checkCommands modelflag ucflag vars (cDecls @ cLimits @ [C.Ass exp;C.CheckSat])
;;  

let checkExpL_FIX ~modelflag ~ucflag ee =
  let myint = Smtsyntax.Sort.Name "Int" in
  let vars = unionL (List.map Exp.fv ee) in
  let cDecls = List.map (fun v -> C.DecVar (v,myint)) vars in
  let eMin = Exp.Int (-1000000) in
  let cLimits = List.map (fun v -> C.Ass (Exp.App("<",[eMin;Exp.Var v]))) vars in
  let cAssExpL = List.map (fun e -> C.Ass e) ee in
    checkCommands modelflag ucflag vars (cDecls @ cLimits @ cAssExpL @ [C.CheckSat])
;;  

(* checkSatExp exp *)
let checkSatExp ~modelflag ~ucflag exp =
  let res =
    try
      checkExp_FIX modelflag ucflag exp
    with
      x -> raise x
  in
  res
;;

let checkSatExpBool exp =
  match checkExp_FIX ~modelflag:false ~ucflag:false exp with
  | Model _ -> true
  | UnsatCore _ -> false
  | _ -> false
;;


let checkSatExpL ~modelflag ~ucflag ee =
  let res =
    try
      checkExpL_FIX modelflag ucflag ee
    with
      x -> raise x
  in
  res
;;


(* checkValidExp exp
checkValidExp E returns true
<-> checkSatExp (-E) returns an unsat_core
<-> (-E) has no model, i.e., (All M. M |/= -E)
<-> (All M. M |= E)
<-> E is valid
*)
let checkValidExp exp =
  match checkSatExp ~modelflag:false ~ucflag:false (not' exp) with
  (* (not exp) is sat <-> A counter-model for exp exists <-> exp is invalid *)
  | Model _ -> false
  (* (not exp) is unsat <-> No counter-model for exp exists <-> exp is valid *)
  | UnsatCore _ -> true 
  | Unknown -> false
;;


(* checkInconsExp exp
checkInconsExp E returns true
<-> checkSatExp E returns an unsat-core, i.e., (All M. M |/= E)
<-> E is inconsistent
*)
let checkInconsExp exp =
  match checkSatExp ~modelflag:false ~ucflag:false exp with
  | Model _ -> false
  | UnsatCore _ -> true
  | Unknown -> false
;;
