(*
  This file provides a translation from slsyntax into smtsyntax
*)

open Tools
open Slsyntax
open Smtsyntax
open Smttoz3
module SatResult = Smttoz3.SatcheckResult

(*----------------------------*)
(* Translation of SL into SMT *)
(*----------------------------*)
(* Non-Presburger expressions are rejected here *)
let mkExp_t (tm : SHterm.t) : Exp.t =
  let rec f_rec t =
    match t with
    | T.Var (v,_) -> Exp.Var v
    | T.Int n -> Exp.Int n
    | T.Add ts ->
	   let ts' = List.map f_rec ts in
	   Exp.App("+",ts')
    | T.Sub ts ->
	   let ts' = List.map f_rec ts in
	   Exp.App("-",ts')
    | T.Mul(t1,t2) ->
       let t1' = f_rec t1 in
       let t2' = f_rec t2 in
	   Exp.App("*",[t1';t2'])
	| T.Mod(t1,t2) ->
	   let t1' = f_rec t1 in
       let t2' = f_rec t2 in
	   Exp.App("mod",[t1';t2'])
    | T.Div(t,T.Int n) ->
	   let t' = f_rec t in
       let n' = Exp.Int n in
	   Exp.App("div",[t';n'])
    | _ ->
       SHterm.println t;
       failwith "Unsupported (out of Presburger)"
  in f_rec tm
;;

(* mkExp_p: making SMT expression for pure formulas *)
let rec mkExp_p p = 
  match p with
  | P.True -> top'
  | P.False -> bot'
  | P.Atom (op,tt) ->
     let ee' = List.map mkExp_t tt in
     begin
       match op with
       | P.Eq -> Exp.App("=",ee')
       | P.Neq -> Exp.App("distinct",ee')
       | P.Le -> Exp.App("<=",ee')
       | P.Lt -> Exp.App("<",ee')
       | P.In ->
          let e' = List.nth ee' 0 in
          let eL' = List.nth ee' 1 in
          let eR' = List.nth ee' 2 in
          let conds_in = [eL' <^= e'; e' <^= eR'] in
          bigAnd' conds_in
       | P.Out ->
          let e' = List.nth ee' 0 in
          let eL' = List.nth ee' 1 in
          let eR' = List.nth ee' 2 in
          let cond_invl = eL' <^= eR' in
          let cond_out = bigOr' [e' <^< eL'; eR' <^< e'] in
          bigAnd' [cond_invl;cond_out]
       | P.Disj ->
          let eL1' = List.nth ee' 0 in
          let eR1' = List.nth ee' 1 in
          let eL2' = List.nth ee' 2 in
          let eR2' = List.nth ee' 3 in
          let cond_invl1 = eL1' <^= eR1' in
          let cond_invl2 = eL2' <^= eR2' in
          let cond_disj = bigOr' [eR1' <^< eL2'; eR2' <^< eL1'] in
          bigAnd' [cond_invl1; cond_invl2; cond_disj]
       | P.Comm ->
          let eL1' = List.nth ee' 0 in
          let eR1' = List.nth ee' 1 in
          let eL2' = List.nth ee' 2 in
          let eR2' = List.nth ee' 3 in
          let cond_invl1 = eL1' <^= eR1' in
          let cond_invl2 = eL2' <^= eR2' in
          let conds_comm = [eL1' <^= eR2'; eL2' <^= eR1'] in
          bigAnd' (cond_invl1 :: cond_invl2 :: conds_comm)
     end
  | P.And pp ->
     let ee = List.map mkExp_p pp in
     bigAnd' ee
  | P.Or pp -> 
     let ee = List.map mkExp_p pp in
     bigOr' ee
  | P.All (vv,p) ->
     let e = mkExp_p p in
     all' vv e
  | P.Ex (vv,p) ->
     let e = mkExp_p p in
     ex' vv e
;;

let isValidPure p =
  let vv = P.fv p in
  (* For avoiding Z3 bug *)
  let eMin = T.Int (-100000) in
  let ppLimits vv = List.map (fun v -> eMin <.< (var v [])) vv in
  let p' = P.And ((ppLimits vv) @ [p]) in
  let q = all' vv (mkExp_p p') in
  match checkSatExp ~modelflag:false ~ucflag:false q with
  | SatResult.Model _ -> true
  | SatResult.UnsatCore _ -> false
  | SatResult.Unknown -> false
;;

let isSatPure p =
  let pp = P.flatten "and" p in
  let p' = P.And pp in
  let q = mkExp_p p' in
  checkSatExp ~modelflag:false ~ucflag:false q
;;

let isSatPureL pp = isSatPure (P.And pp)
;;  

let isUnsatPure p =
  match isSatPure p with
  | SatResult.Model _ -> false
  | SatResult.UnsatCore _ -> true
  | SatResult.Unknown -> false
;;

let isUnsatPureL pp = isUnsatPure (P.And pp)
;;  

(* entailPure [p1;p2] p checks p1,p2|=p *)
(* It is equivalent to (-p1 or -p2 or p) is valid *)
let entailPure pp p =
  let p' = P.Or (p::(List.map P.dual pp)) in
  isValidPure p'
;;

(*---------------------------*)
(* simplifying Pure-formulas *)
(*---------------------------*)
(* p -> True (p : valid) *)
(* p -> False (p : unsat) *)
(* p -> False (p : not sanitary) *)
(* And (True :: pp) -> And pp *)
(* And [p] -> p *)
(* And [] -> True *)
(* Or (False :: pp) -> Or pp *)
(* Or [p] -> p *)
(* Or [] -> False *)
(* For efficiency, this simplification is done only for the topmost And and Or *)
let simplifyPure p =
  match p with
  | P.And pp ->
     let _pp = ref [] in
     let _res = ref P.True in
     begin
       try
         for i = 0 to List.length pp - 1 do
           let p = List.nth pp i in
           match isUnsatPure p, isValidPure p with
           | true,_ -> raise Exit
           | _,true -> ()
           | _,_ -> _pp := p :: !_pp
         done;
         _res := P.And (List.rev !_pp)
       with
         Exit -> _res := P.False
     end;
     !_res
  | P.Or pp ->
     let _pp = ref [] in
     let _res = ref P.False in
     begin
       try
         for i = 0 to List.length pp - 1 do
           let p = List.nth pp i in
           match isValidPure p, isUnsatPure p with
           | true,_ -> raise Exit
           | _,true -> ()
           | _,_ -> _pp := p :: !_pp
         done;
         _res := P.Or (List.rev !_pp)
       with
         Exit -> _res := P.True
     end;
     !_res
  | _ -> p
;;

(* u in [t,t] is replaced by t = u *)
let rec simplifyPureAtom p =
  match p with
  | P.And pp -> P.And (simplifyPureAtomL pp)
  | P.Or pp -> P.Or (simplifyPureAtomL pp)
  | _ -> p
and simplifyPureAtomL pp =
  match pp with
  | [] -> []
  | (P.Atom (P.In,u::t1::t2::_))::pp' when t1 = t2 -> (u =.= t1)::(simplifyPureAtomL pp')
  | (P.Atom (P.Out,u::t1::t2::_))::pp' when t1 = t2 -> (u <.> t1)::(simplifyPureAtomL pp')
  | (P.Atom (P.Comm,t1::t2::u1::u2::_))::pp' when t1 = t2 && u1 = u2 -> (t1 =.= u1)::(simplifyPureAtomL pp')
  | (P.Atom (P.Disj,t1::t2::u1::u2::_))::pp' when t1 = t2 && u1 = u2 -> (t1 <.> u1)::(simplifyPureAtomL pp')
  | p::pp' -> (simplifyPureAtom p)::(simplifyPureAtomL pp')
;;


(* reducePureL [p1;p2;p3] *)
(* It drops p1 if [p2;p3] -> p1 is valid *)
(* Repeat this until the list is not reducible *)
let reducePureL pp =
  let isReducible pp0 p0 =
    let vv = unionL (List.map P.fv (p0::pp0)) in
    let ee0 = List.map mkExp_p pp0 in
    let e0 = mkExp_p p0 in
    let q = all' vv (bigAnd' ee0 -^> e0) in
    match checkSatExp ~modelflag:false ~ucflag:false q with
    | SatResult.Model _ -> true
    | SatResult.UnsatCore _ -> false
    | SatResult.Unknown -> false
  in
  let _tmpPP = ref pp in
  let _prePP = ref [] in
  while !_tmpPP <> !_prePP do
    _prePP := !_tmpPP;
    try
      for i = 0 to List.length !_tmpPP - 1 do
        let (p1,pp1) = List_tailrec.takeNth !_tmpPP i in
        match isReducible pp1 p1 with
        | true -> _tmpPP := pp1; raise Skip
        | false -> ()
      done;
    with
      Skip -> ()
  done;
  match !_tmpPP with
  | [] -> [P.True]
  | _ -> !_tmpPP
;;
