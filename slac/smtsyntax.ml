open Tools;;

module Logic = struct

  type t =
  | AUFLIA | AUFLIRA | AUFNIRA
  | LIA | LRA
  | QF_ABV | QF_AUFBV | QF_AUFLIA | QF_AX | QF_BV | QF_IDL
  | QF_LIA | QF_LRA | QF_NIA | QF_NRA | QF_RDL
  | QF_UF | QF_UFBV| QF_UFIDL | QF_UFLIA | QF_UFLRA | QF_UFNRA
  | UFLRA | UFNIA
    

  let to_string logic = match logic with
    | AUFLIA -> "AUFLIA"
    | AUFLIRA -> "AUFLIRA"
    | AUFNIRA -> "AUFNIRA"
    | LIA -> "LIA"
    | LRA -> "LRA"
    | QF_ABV -> "QF_ABV"
    | QF_AUFBV -> "QF_AUFBV"
    | QF_AUFLIA -> "QF_AUFLIA"
    | QF_AX -> "QF_AX"
    | QF_BV -> "QF_BV"
    | QF_IDL -> "QF_IDL"
    | QF_LIA -> "QF_LIA"
    | QF_LRA -> "QF_LRA"
    | QF_NIA -> "QF_NIA"
    | QF_NRA -> "QF_NRA"
    | QF_RDL -> "QF_RDL"
    | QF_UF -> "QF_UF"
    | QF_UFBV -> "QF_UFBV"
    | QF_UFIDL -> "QF_UFIDL"
    | QF_UFLIA -> "QF_UFLIA"
    | QF_UFLRA -> "QF_UFLRA"
    | QF_UFNRA -> "QF_UFNRA"
    | UFLRA -> "UFLRA"
    | UFNIA -> "UFNIA"
      
end
;;

module Sort = struct

  type t = Name of string | App of string * t list
  type sub = (string * t) list

  let rec to_string s = match s with 
    | Name s -> s
    | App(hd,sorts) -> 
      let sorts' = string_of_list to_string " " sorts in
      "("^hd^" "^sorts'^")"

  let rec subst (sb : sub) s = match s with
    | Name v as q ->
      begin
      try
	List.assoc v sb 
      with Not_found -> q
      end
    | App(hd,sorts) ->
      let sorts' = List.map (subst sb) sorts in
      App(hd,sorts')

  let rec ctxSortSub (p,vars,s) sort =
    match sort with
    | Name _ as q -> q
    | App(q,sorts) when q = p ->
      let sorts' = List.map (ctxSortSub (p,vars,s)) sorts in
      let sub = zipLst vars sorts' in
      subst sub s
    | App(q,sorts) ->		(* when q <> p *)
      let sorts' = List.map (ctxSortSub (p,vars,s)) sorts in
      App(q,sorts')
	
end
;;

module Keyword = struct

  type t = K0 of string | K1 of string
  (* K0 "abc" comes from ":abc" *)
  (* K1 "abc" comes from  "abc" *)

  let to_string kw = match kw with
    | K0 kwd -> ":"^kwd
    | K1 kwd -> kwd

end
;;

module Exp = struct

  type t =
  | Int of int
  | Var of string
  | App of string * t list
  | All of (string * Sort.t) list * t
  | Ex of (string * Sort.t) list * t
  | Let of (string * t) list * t
  | Att of t * attriv list
  and attriv = Keyword.t * t list

  type sub = (string * t) list

  let rec fv e =
    let fv_att (kw,exps) = unionL (List.map fv exps) in
    match e with
    | Int _ -> []
    | Var v -> [v]
    | App(_,exps) -> unionL (List.map fv exps)
    | All(vs,exp) ->
      let fv1 = fv exp in
      let vars = List.map (fun (x,_) -> x) vs in
      List.filter (fun x -> not(List.mem x vars)) fv1
    | Ex(vs,exp) ->
      let fv1 = fv exp in
      let vars = List.map (fun (x,_) -> x) vs in
      List.filter (fun x -> not(List.mem x vars)) fv1
    | Let(binds,exp) ->
      let fv0 = fv exp in
      let vars = List.map (fun (x,_) -> x) binds in
      let fv0' = List.filter (fun x -> not(List.mem x vars)) fv0 in
      let fv1 = List.concat(List.map (fun (_,e) -> fv e) binds) in
      union fv0' fv1
    | Att(exp,atts) ->
      let fvatt = List.concat(List.map fv_att atts) in
      let fvexp = fv exp in
      union fvatt fvexp

  let rec fbv e =
    let fbv_att(kw,exps) = unionL (List.map fbv exps) in
    match e with
    | Int _ -> []
    | Var v -> [v]
    | App(_,exps) -> unionL (List.map fbv exps)
    | All(vss,exp) ->
      let vs' = List.map (fun (x,_) -> x) vss in
      let fbv' = fbv exp in
      union vs' fbv'
    | Ex(vss,exp) ->
      let vs' = List.map (fun (x,_) -> x) vss in
      let fbv' = fbv exp in
      union vs' fbv'
    | Let(binds,exp) ->
      let vs0 = fbv exp in
      let vs1 = List.map (fun (x,_) -> x) binds in
      let vs2 = List.concat (List.map (fun (_,e) -> fbv e) binds) in
      unionL [vs0;vs1;vs2]
    | Att(exp,atts) ->
      let vs0 = fbv exp in
      let vs1 = List.concat (List.map fbv_att atts) in
      union vs0 vs1

  let rec subst0 repl exp =
    let subst0_att rp (kw,exps) = (kw,List.map (subst0 rp) exps) in
    match exp with
    | Int _ as q -> q
    | Var v as q ->
      begin
	try
	  Var (List.assoc v repl)
	with Not_found -> q
      end
    | App(f,args) ->
      let args' = List.map (subst0 repl) args in
      App(f,args')
    | All(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let repl' = List.filter (fun (x,_) -> not(List.mem x vs)) repl in
      let exp' = subst0 repl' exp in
      All(vss,exp')
    | Ex(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let repl' = List.filter (fun (x,_) -> not(List.mem x vs)) repl in
      let exp' = subst0 repl' exp in
      Ex(vss,exp')
    | Let(binds,exp) ->
      let binds' = List.map (fun (v,e)-> (v,(subst0 repl e))) binds in
      let vs = List.map (fun (v,_)->v) binds in
      let repl' = List.filter (fun (x,_) -> not(List.mem x vs)) repl in
      let exp' = subst0 repl' exp in
      Let(binds',exp')
    | Att(exp,atts) ->
      let exp' = subst0 repl exp in
      let atts' = List.map (subst0_att repl) atts in
      Att(exp',atts')

  let rec subst1 sub used exp =
    let rec mk_vlist avoid usd vs = match vs with
      | [] -> ([],[])
      | v::vs1 ->
	if List.mem v avoid then
	  let v' = genFreshVar "v" usd in
	  let usd' = v'::usd in
	  let (vs2,sub) = mk_vlist avoid usd' vs1 in
	  (v'::vs2,(v,v')::sub)
	else
	  let (vs2,sub) = mk_vlist avoid usd vs1 in
	  (v::vs2,sub)
    in
    let subst1_att sb usd (kw,exps) = (kw,List.map (subst1 sb usd) exps) in
    match exp with
    | Int _ as q -> q
    | Var v as q ->
      begin
	try
	  List.assoc v sub
	with Not_found -> q
      end
    | App(f,args) ->
      let args' = List.map (subst1 sub used) args in
      App(f,args')
    | All(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let ss = List.map (fun (_,s)->s) vss in
      let vars = fbv exp in
      let avoid = List.concat (List.map (fun (_,e)->fv e) sub) in
      let used' = vars@vs@used in
      let (vs',repl) = mk_vlist avoid used' vs in
      let exp' = subst0 repl exp in
      let sub' = List.filter (fun (x,_)-> not(List.mem x vs)) sub in
      let exp'' = subst1 sub' used' exp' in
      let vss' = zipLst vs' ss in
      All(vss',exp'')
    | Ex(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let ss = List.map (fun (_,s)->s) vss in
      let vars = fbv exp in
      let avoid = List.concat (List.map (fun (_,e)->fv e) sub) in
      let used' = vars@vs@used in
      let (vs',repl) = mk_vlist avoid used' vs in
      let exp' = subst0 repl exp in
      let sub' = List.filter (fun (x,_)-> not(List.mem x vs)) sub in
      let exp'' = subst1 sub' used' exp' in
      let vss' = zipLst vs' ss in
      Ex(vss',exp'')
    | Let(binds,exp) ->
      let vs = List.map (fun (x,_)->x) binds in
      let exps = List.map (fun (_,e)->e) binds in
      let vars = fbv exp in
      let avoid = List.concat (List.map (fun (_,e)->fv e) sub) in
      let used' = vars@vs@used in
      let (vs',repl) = mk_vlist avoid used' vs in      
      let exp' = subst0 repl exp in
      let sub' = List.filter (fun (x,_)-> not(List.mem x vs)) sub in 
      let exp'' = subst1 sub' used' exp' in
      let binds' = zipLst vs' exps in
      Let(binds',exp'')
    | Att(exp,atts) ->
      let exp' = subst1 sub used exp in
      let atts' = List.map (subst1_att sub used) atts in
      Att(exp',atts')

  let subst (sb : sub) exp =
    let vars = List.concat (List.map (fun (_,e)->fbv e) sb) in
    subst1 sb vars exp

  let rec ctxSortSub csub exp = 
    match exp with
    | Int _ as q -> q
    | Var v as q -> q
    | App(f,args) ->
      let args' = List.map (ctxSortSub csub) args in
      App(f,args')
    | All(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let ss = List.map (fun (_,s) -> s) vss in
      let ss' = List.map (Sort.ctxSortSub csub) ss in
      let exp' = ctxSortSub csub exp in
      let vss' = zipLst vs ss' in
      All(vss',exp')
    | Ex(vss,exp) ->
      let vs = List.map (fun (x,_)->x) vss in
      let ss = List.map (fun (_,s) -> s) vss in
      let ss' = List.map (Sort.ctxSortSub csub) ss in
      let exp' = ctxSortSub csub exp in
      let vss' = zipLst vs ss' in
      Ex(vss',exp')
    | Let(binds,exp) ->
      let binds' = List.map (fun (v,e)-> (v,ctxSortSub csub e)) binds in
      let exp' = ctxSortSub csub exp in
      Let(binds',exp')
    | Att(exp,atts) ->
      let exp' = ctxSortSub csub exp in
      let atts' = List.map (ctxSortSub_att csub) atts in
      Att(exp',atts')
  and ctxSortSub_att csub (kw,exps) =
    let exps' = List.map (ctxSortSub csub) exps in
    (kw,exps')

  (* Pretty-printing in smt2-format *)
  let rec to_string exp =
    match exp with
    | Var v -> v
    | Int n -> string_of_int n
    | App(func,args) ->
      let args' = string_of_list to_string " " args in
      "("^func^" "^args'^")"
    | All(varst,e) ->
      let e' = to_string e in
      let stringvarst (v,s) = "("^v^" "^(Sort.to_string s)^")" in
      let varst' = string_of_list stringvarst " " varst in
      let varst'' = "("^varst'^")" in
      "(forall "^varst''^" "^e'^")"
    | Ex(varst,e) ->
      let e' = to_string e in
      let stringvarst (v,s) = "("^v^" "^(Sort.to_string s)^")" in
      let varst' = string_of_list stringvarst " " varst in
      let varst'' = "("^varst'^")" in
      "(exists "^varst''^" "^e'^")"
    | Let(binds,e) ->
      let e' = to_string e in
      let string_of_bind (v,e) = "("^v^" "^(to_string e)^")" in
      let binds' = string_of_list string_of_bind " " binds in
      "(let "^binds'^" "^e'^")"
    | Att(e,atts) ->
      let e' = to_string e in
      let atts' = string_of_list to_string_att " " atts in
      "(! "^e'^" "^atts'^")"
  and to_string_att (kw,exps) =
    let kw' = Keyword.to_string kw in
    let exps' = string_of_list to_string " " exps in
    kw'^" "^exps'
      
  let print exp = print_string (to_string exp)

  let println exp = print_string ((to_string exp)^"\n")

  (* Pretty-printing in simple-format *)
  let rec to_string_s exp =
    match exp with
    | Var v -> v
    | Int n -> string_of_int n
    | App(func,args) ->
      begin
      match func with
      | "+" -> string_of_list to_string_s "+" args
      | "-" -> string_of_list to_string_s "-" args
      | "*" -> string_of_list to_string_s "*" args
	  | "mod" -> string_of_list to_string_s "%" args
      | "=" -> string_of_list to_string_s " = " args
      | "<" -> string_of_list to_string_s " < " args
      | "<=" -> string_of_list to_string_s " <= " args
      | "=>" -> "("^(string_of_list (fun e -> "("^(to_string_s e)^")") " => " args)^")"
      | "and" -> string_of_list to_string_s (" & ") args
      | "not" -> "~("^(to_string_s (List.hd args))^")"
      | _ -> 
	let args' = string_of_list to_string_s " " args in
	"("^func^" "^args'^")"
      end 
    | All(varst,e) ->
      let e' = to_string_s e in
      let vars = List.map (fun (v,_) -> v) varst in
      let vars' = string_of_list (fun x -> x) "," vars in
      "All "^vars'^".("^e'^")"
    | Ex(varst,e) ->
      let e' = to_string_s e in
      let vars = List.map (fun (v,_) -> v) varst in
      let vars' = string_of_list (fun x -> x) "," vars in
      "Ex "^vars'^".("^e'^")"
    | Let(_,_) -> "let"
    | Att(e,atts) -> "att"

  let print_s exp = print_string (to_string_s exp)

  let println_s exp = print_string ((to_string_s exp)^"\n")

end
;;

module Command = struct

  type t =
  | DecVar of string * Sort.t
  (* (declare-var <sym> <sort>) *)
  | DecCons of string * Sort.t
  (* (declare-const <sym> <sort>) *)
  | DecFn of string * Sort.t list * Sort.t	
  (* (declare-fun <sym> <sort>* <sort>) *)
  | DecFns of (string * Sort.t list) list
  (* (declare-funs ( <sym> <sort>* )* *)
  | DefFn of string * (string * Sort.t) list * Sort.t * Exp.t
  (* (define-fun <sym> (<sym> <sort>)* <sort> <exp>) *)
  | DecSt of string * int
  (* (declare-sort <sym> <num>?) *)
  (* (declare-sort <sym>) is (declare-sort <sym> 0)*)
  | DefSt of string * string list * Sort.t
  (* (define-sort <sym> (<sym>* ) <sort>) *)
  | DecPreds of (string * Sort.t list) list
  (* (declare-preds ( ( <sym> <sort>* )* )) *)
  | Ass of Exp.t
  (* (assert <exp>) *)
  | GetAss
  (* (get-assertions) *)
  | CheckSat
  (* (check-sat) *)
  | GetPrf
  (* (get-proof) *)
  | GetUnsat
  (* (get-unsat-core) *)
  | GetVal of Exp.t list
  (* (get-value <exp>* ) *)
  | GetAsgn
  (* (get-assignment) *)
  | GetOpt of Keyword.t
  (* (get-option <keyword>) *)
  | SetOpt of Keyword.t * Exp.t
  (* (set-option <keyword> <exp>) *)
  | GetInfo of Keyword.t
  (* (get-info <keyword>) *)
  | SetInfo of Keyword.t * Exp.t
  (* (set-info <keyword> <attval>) *)
  | Exit
  (* (exit) *)      
  | Push of int option
  (* (push) *)
  | Pop of int option
  (* (pop) *)
  | Echo of string
  (* (echo <string>) *)
  | GetModel
  (* (get-model) *)
  | Reset
  (* (reset) *)
  | Display of Exp.t
  (* (display <exp>) *)
  | Simpfy of Exp.t * Exp.attriv list
  (* (simplify <exp> <attriv>* ) *)
  | Eval of Exp.t * (Keyword.t * Exp.t) list
  (* (eval <exp> (<keyword> <exp>)* ) *)
  | Model
  (* (model) *)
  | DecDT of (string list * datatype list)
  (* (declare-datatypes (<sym>* ) (<datatype>)* )	*)
  (* <datatype> = (<sym> (<cons_decl>)* )		*)
  (* <cons_decl> = (<sym> (<acc_decl>)* )		*)
  (* <acc_decl> = (<sym> <sort>)			*)
  and datatype = string * cons_decl list
  and cons_decl = string * acc_decl list
  and acc_decl = string * Sort.t
  (* Example of datatypes				*)
  (* (declare-datatypes () ((pair (mk_pair (fst Int) (snd Int)))) *)
  (* This means  pair ::= mk_pair of (fst:Int) * (snd:Int) *)
    
  exception Sort_found
    
  let rec getSort_of_symbol coms sym =
    if coms = [] then (raise Not_found) else
      let hdcoms = List.hd coms in
      let tlcoms = List.tl coms in
      let res = ref (Sort.Name "") in
      try
	match hdcoms with
	| DecVar(sym1,sort1) 
	| DecCons(sym1,sort1) 
	| DecFn(sym1,_,sort1) ->
	  if sym = sym1
	  then
	    (res := sort1; raise Sort_found)
	  else getSort_of_symbol tlcoms sym
	| DecFns funinfo ->
	  begin
	    try
	      (res := List.hd(List.rev(List.assoc sym funinfo));
	       raise Sort_found)
	    with Not_found -> getSort_of_symbol tlcoms sym
	  end
	| DecPreds predinfo ->
	  begin
	    try
	      if List.length (List.assoc sym predinfo) >= 0 then
		(res := Sort.Name "Bool";
		 raise Sort_found)
	      else Sort.Name "dummy";
	    with Not_found -> getSort_of_symbol tlcoms sym
	  end
	| DefFn(sym1,_,sort1,_) ->
	  if sym = sym1
	  then
	    (res := sort1; raise Sort_found)
	  else getSort_of_symbol tlcoms sym	  
	| _ -> getSort_of_symbol tlcoms sym
      with Sort_found -> !res

  let getSort_of_exp coms exp =
    let module E = Exp in
    let rec getSort e = 
    match e with
    | E.Var v -> getSort_of_symbol coms v
    | E.Int _ -> Sort.Name "Int"
    | E.App(f,_) -> getSort_of_symbol coms f
    | E.All _ -> Sort.Name "Bool"
    | E.Ex _ -> Sort.Name "Bool"
    | E.Let(_,e') -> getSort e'
    | E.Att(e',_) -> getSort e'
    in
    getSort exp

  let rec ctxSortSub csub com = match com with
    | DecVar(sym,sort) -> 
      let sort' = Sort.ctxSortSub csub sort in
      DecVar(sym,sort')
    | DecCons(sym,sort) ->
      let sort' = Sort.ctxSortSub csub sort in
      DecCons(sym,sort')
    | DecFn(sym,sorts,sort) -> 
      let sorts' = List.map (Sort.ctxSortSub csub) sorts in
      let sort' = Sort.ctxSortSub csub sort in
      DecFn(sym,sorts',sort')	
    | DecFns fdecs ->
      let ctxSub (f,sorts) =
	let sorts' = List.map (Sort.ctxSortSub csub) sorts in
	(f,sorts')
      in
      let fdecs' = List.map ctxSub fdecs in
      DecFns fdecs'
   | DefFn(sym,args,sort,exp) -> 
     let sort' = Sort.ctxSortSub csub sort in
     let exp' = Exp.ctxSortSub csub exp in
     let args' =
       List.map (fun (x,s) -> (x, Sort.ctxSortSub csub s)) args
     in
     DefFn(sym,args',sort',exp')
   | DecSt(_,_) as q -> q
   | DefSt(sym,syms,sort) ->
     let sort' = Sort.ctxSortSub csub sort in
     DefSt(sym,syms,sort')
   | DecPreds pdecs ->
     let ctxSub (p,sorts) = (p,List.map (Sort.ctxSortSub csub) sorts)
     in 
     let pdecs' = List.map ctxSub pdecs in
     DecPreds pdecs'
   | Ass exp ->
     let exp' = Exp.ctxSortSub csub exp in
     Ass exp'
  | GetAss as q -> q
  | CheckSat as q -> q
  | GetPrf as q -> q
  | GetUnsat as q -> q
  | GetVal exps ->
    let exps' = List.map (Exp.ctxSortSub csub) exps in
    GetVal exps'
  | GetAsgn as q -> q
  | GetOpt _ as q -> q
  | SetOpt(kw,exp) -> 
    let exp' = Exp.ctxSortSub csub exp in
    SetOpt(kw,exp')
  | GetInfo _ as q -> q
  | SetInfo(kw,exp) ->
    let exp' = Exp.ctxSortSub csub exp in
    SetInfo(kw,exp')
  | Exit as q -> q
  | Push _ as q -> q
  | Pop _ as q -> q
  | Echo _ as q -> q
  | GetModel as q -> q
  | Reset as q -> q
  | Display exp -> 
    let exp' = Exp.ctxSortSub csub exp in
    Display exp'
  | Simpfy(exp,attrs) -> 
    let exp' = Exp.ctxSortSub csub exp in
    let attrs' = List.map (Exp.ctxSortSub_att csub) attrs in
    Simpfy(exp',attrs')
  | Eval(exp,kwexps) ->
    let exp' = Exp.ctxSortSub csub exp in
    let ctxSub_kwex (kw,e) =
      let e' = Exp.ctxSortSub csub e in
      (kw,e')
    in
    let kwexps' = List.map ctxSub_kwex kwexps in
    Eval(exp',kwexps')
  | Model as q -> q
  | DecDT(syms, dtypes) ->
    let dtypes' = List.map (ctxSub_dtype csub) dtypes in
    DecDT(syms, dtypes')
  and ctxSub_dtype csub (sym,cdecls) =
    let cdecls' = List.map (ctxSub_consdecl csub) cdecls in
    (sym,cdecls')
  and ctxSub_consdecl csub (sym,adecls) = 
    let adecls' = List.map (ctxSub_accdecl csub) adecls in
    (sym,adecls')
  and ctxSub_accdecl csub (sym,sort) = 
    let sort' = Sort.ctxSortSub csub sort in
    (sym,sort')

      
  let rec to_string com = match com with
    | DecVar(sym,sort) -> 
      let sort' = Sort.to_string sort in
      "(declare-var "^sym^" "^sort'^")"
    | DecCons(sym,sort) ->
      let sort' = Sort.to_string sort in
      "(declare-const "^sym^" "^sort'^")"
    | DecFn(sym,sorts,sort) -> 
      let sorts' = string_of_list Sort.to_string " " sorts in
      let sort' = Sort.to_string sort in
      "(declare-fun "^sym^" ("^sorts'^") "^sort'^")"
    | DecFns fdecs ->
      let to_string_fdec (f,sorts) =
	let sorts' = string_of_list Sort.to_string " " sorts in
	"("^f^" "^sorts'^")"
      in
      let fdecs' = string_of_list to_string_fdec " " fdecs in
      "(declare-funs ("^fdecs'^"))"
   | DefFn(sym,args,sort,exp) -> 
     let sort' = Sort.to_string sort in
     let exp' = Exp.to_string exp in
     let args' =
      let tostr1 = fun (x,s) -> "("^x^" "^(Sort.to_string s)^")" in
      string_of_list tostr1 " " args
     in
     "(define-fun "^sym^" ("^args'^") "^sort'^" "^exp'^")"
   | DecSt(sym,n) -> "(declare-sort "^sym^" "^(string_of_int n)^")"
   | DefSt(sym,syms,sort) ->
     let sort' = Sort.to_string sort in
     let syms' = string_of_list (fun x->x) " " syms in
     "(define-sort "^sym^" ("^syms'^") "^sort'^")"
   | DecPreds pdecs ->
     let to_string_pdec (p,sorts) =
       let sorts' = string_of_list Sort.to_string " " sorts in
       if sorts = [] then "("^p^")" else 
       "("^p^" "^sorts'^")"
     in
     let pdecs' = string_of_list to_string_pdec " " pdecs in
     "(declare-preds ("^pdecs'^"))"
  | Ass exp -> "(assert "^(Exp.to_string exp)^")"
  | GetAss -> "(get-assertions)"
  | CheckSat -> "(check-sat)"
  | GetPrf -> "(get-proof)"
  | GetUnsat -> "(get-unsat-core)"
  | GetVal exps ->
    let exps' = string_of_list Exp.to_string " " exps in
    "(get-value "^exps'^")"
  | GetAsgn -> "(get-assignment)"
  | GetOpt kw -> "(get-option "^(Keyword.to_string kw)^")"
  | SetOpt(kw,exp) -> 
    let kw' = Keyword.to_string kw in
    let exp' = Exp.to_string exp in
    "(set-option "^kw'^" "^exp'^")"
  | GetInfo kw ->
    let kw' = Keyword.to_string kw in
    "(get-info "^kw'^")"
  | SetInfo(kw,exp) -> 
    let kw' = Keyword.to_string kw in
    let exp' = Exp.to_string exp in
    "(set-info "^kw'^" "^exp'^")"
  | Exit -> "(exit)"      
  | Push opt ->
    begin
      match opt with
      | None -> "(push)"
      | Some n -> "(push "^(string_of_int n)^")"
    end
  | Pop opt ->
    begin
      match opt with
      | None -> "(pop)"
      | Some n -> "(pop "^(string_of_int n)^")"
    end
  | Echo str -> "(echo "^str^")"
  | GetModel -> "(get-model)"      
  | Reset -> "(reset)"
  | Display exp -> 
    let exp' = Exp.to_string exp in
    "(display "^exp'^")"
  | Simpfy(exp,attrs) -> 
    let exp' = Exp.to_string exp in
    let attrs' = string_of_list Exp.to_string_att " " attrs in
    if List.length attrs = 0 then "(simplify "^exp'^")"
    else "(simplify "^exp'^" "^attrs'^")"
  | Eval(exp,kwexps) ->
    let to_string_kwexp (kw,e) =
      let kw' = Keyword.to_string kw in
      let e' = Exp.to_string e in
      "("^kw'^" "^e'^")"
    in
    let kwexps' = string_of_list to_string_kwexp " " kwexps in
    let kwexps'' = if kwexps = [] then "" else " "^kwexps' in
    let exp' = Exp.to_string exp in
    "(eval "^exp'^kwexps''^")"
  | Model -> "(model)"
  | DecDT(syms, dtypes) ->
    let syms' = string_of_list (fun x->x) " " syms in
    let dtypes' = string_of_list to_string_datatype " " dtypes in
    "(declare-datatypes ("^syms'^") ("^dtypes'^"))"
  and to_string_datatype (sym,cdecls) =
    let cdecls' = string_of_list to_string_consdecl " " cdecls in
    if cdecls = [] then sym else "("^sym^" "^cdecls'^")"
  and to_string_consdecl (sym,adecls) = 
    let adecls' = string_of_list to_string_accdecl " " adecls in
    if adecls = [] then sym else "("^sym^" "^adecls'^")"
  and to_string_accdecl (sym,sort) = 
    let sort' = Sort.to_string sort in
    "("^sym^" "^sort'^")"

  let println com = print_endline (to_string com)
                    
end
;;

module SMTprog = struct

  type t = Logic.t * Command.t list

  let to_string (prog : t) = 
    let (logic,commands) = prog in
    let logic' = "(set-logic "^(Logic.to_string logic)^")" in
    let commands' = 
	List.fold_right
	(fun c->fun x-> 
		if x = "" then Command.to_string c 
		else (Command.to_string c)^"\n"^x)
	commands
	""
    in logic'^"\n\n"^commands'

  let print prog = print_string ((to_string prog)^"\n")

end
;;

(*--------------------------------------*)
(* Short-cuts for SMT-expressions	    *)
(*--------------------------------------*)
let ( =^= ) t1 t2 = Exp.App("=",[t1;t2])   (* eq *)
;;
let ( <^> ) t1 t2 = Exp.App("distinct",[t1;t2])   (* neq *)
;;
let ( >^= ) t1 t2 = Exp.App(">=",[t1;t2])  (* geq*)
;;
let ( <^= ) t1 t2 = Exp.App("<=",[t1;t2])  (* leq *)
;;
let ( <^< ) t1 t2 = Exp.App("<",[t1;t2])   (* lt *)
;;
let ( %^% ) t1 t2 = Exp.App("mod",[t1;t2])  (* t1 mod t2 *)
;;
let zero' = Exp.Int 0
;;
let bot' = Exp.App("distinct",[zero';zero']) (* false *)
;;
let top' = Exp.App("=",[zero';zero'])  (* true *)
;;
let not' e = Exp.App("not",[e])  (* negation *)
;;
let ( -^> ) e1 e2 = Exp.App("imp",[e1;e2]) (* imply *)
;;
let ( &^& ) e1 e2 = Exp.App("and",[e1;e2])  (* e1 and e2 *)
;;
let ( |^| ) e1 e2 = Exp.App("or",[e1;e2])  (* e1 and e2 *)
;;
let bigOr' ee =
  match List.length ee with
  | 0 -> bot'
  | 1 -> List.hd ee
  | _ -> Exp.App("or",ee)
;;
let bigAnd' ee =
  match List.length ee with
  | 0 -> top'
  | 1 -> List.hd ee
  | _ -> Exp.App("and",ee)
;;
let int' = Sort.Name "Int"
;;
let all' vv e =
  let vss = List.map (fun v -> (v,int')) vv in
  let conds = List.map (fun v -> zero' <^= (Exp.Var v)) vv in
  let cond = bigAnd' conds in
  match List.length vv with
  | 0 -> e
  | _ -> Exp.All(vss, cond -^> e)
;;
let ex' vv e =
  let vss = List.map (fun v -> (v,int')) vv in
  let conds = List.map (fun v -> zero' <^= (Exp.Var v)) vv in
  let body = bigAnd' (conds@[e]) in
  match List.length vv with
  | 0 -> e
  | _ -> Exp.Ex(vss, body)
;;
