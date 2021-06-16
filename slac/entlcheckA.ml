(* Brotherston's decision procedure *)
open Tools
open Slsyntax
open Smtsyntax
open Sltosmt
open Smttoz3
module SatResult = Smttoz3.SatcheckResult
;;

(*------------------------------*)
(* Brotherston's translation    *)
(*------------------------------*)
   (*
(* gamma1 [(a1,b1);(a2,b2)]	makes		*)
(* 0 < a1<=b1 & 0 < a2<=b2 & (b1<a2 or b2<a1) *)
let gamma_1 plist =
  let elist = ref [] in
  for i = 0 to List.length plist - 1 do
    let (t,u) = List.nth plist i in
    let a = mkExp_t t in
    let b = mkExp_t u in
    let z = mkExp_t (num 0) in
    elist := (z <^< a) :: (a <^= b) :: !elist;
  done;
  for i = 0 to List.length plist - 1 do
    for j = i+1 to List.length plist - 1 do
      let (t1,u1) = List.nth plist i in
      let (t2,u2) = List.nth plist j in
      let a1,b1 = mkExp_t t1, mkExp_t u1 in
      let a2,b2 = mkExp_t t2, mkExp_t u2 in
      elist := ((b1 <^< a2) |^| (b2 <^< a1)) :: !elist;
    done;
  done;
  !elist
;;

let rec mkPlist ss1 =
  match ss1 with
  | [] -> []
  | S.Pto(t,_)::ss2 -> (t,t)::(mkPlist ss2)
  | S.Arr(t,u)::ss2 -> (t,u)::(mkPlist ss2)
  | S.Str(t,u)::ss2 -> (t,u)::(mkPlist ss2)
;;

let gamma_2 ss = gamma_1 (mkPlist ss)
;;

(* Brotherston's gamma *)
(* s |= gamma(sh) iff  s,h |= sh for some h *)
let gamma (sh : QFSH.t) =
  let (p,ss) = sh in
  let ee = gamma_2 ss in
  let e = mkExp_p p in
  bigAnd' (e :: ee)
;;
    *)
   
(* Brotherston's psi1 *)
let psi1_core (ss1: SHspat.t) (ss2 : SHspat.t) = 
  let elist = ref [] in
  for i = 0 to List.length ss1 - 1 do
    for j = 0 to List.length ss2 - 1 do
      let s1 = List.nth ss1 i in
      let s2 = List.nth ss2 j in
      match s1,s2 with
      | S.Arr(t1,u1),S.Pto(v,_) ->
	     let a1 = mkExp_t t1 in
	     let b1 = mkExp_t u1 in
	     let c = mkExp_t v in
	     let d = (a1 <^= c) &^& (c <^= b1) in
	     elist := d :: !elist;
      | S.Str(t1,u1),S.Pto(v,_) ->
	     let a1 = mkExp_t t1 in
	     let b1 = mkExp_t u1 in
	     let c = mkExp_t v in
	     let d = (a1 <^= c) &^& (c <^= b1) in
	     elist := d :: !elist;
      | _,_ -> ()
    done;
  done;
  bigOr' !elist
;;

let psi1 (sh1 : QFSH.t) (sh2 : QFSH.t) =
  let (_,ss1) = sh1 in
  let (_,ss2) = sh2 in
  psi1_core ss1 ss2
;;

(* Brotherston's psi2 *)
let psi2_core (ss1: SHspat.t) (ss2 : SHspat.t) = 
  let elist = ref [] in
  for i = 0 to List.length ss1 - 1 do
    for j = 0 to List.length ss2 - 1 do
      let s1 = List.nth ss1 i in
      let s2 = List.nth ss2 j in
      match s1,s2 with
      | S.Pto(u1,cc1),S.Pto(u2,cc2) ->
         (* pointer-part *)
	     let a1 = mkExp_t u1 in
	     let a2 = mkExp_t u2 in
         let e = (a1 =^= a2) in
         (* contents-part *)
         let flds = dropRed @@ List.map fst (cc1 @ cc2) in
         let ee =
           List.map
             (fun f ->
               match findItemOption f cc1, findItemOption f cc2 with
               | None,_ -> top'
               | _,None -> top'
               | Some t1,Some t2 -> (mkExp_t t1) <^> (mkExp_t t2)
             )
             flds
         in
	     let e1 = e &^& (bigOr' ee) in
	     elist := e1 :: !elist;
      | _,_ -> ()	
    done;
  done;
  bigOr' !elist
;;

let psi2 sh1 sh2 =
  let (_,ss1) = sh1 in
  let (_,ss2) = sh2 in
  psi2_core ss1 ss2
;;

(* making phi *)
(* s |= phi sh1 sh2 means "there is a cell that is covered by sh1 but not covered by sh2" *)
let phi_1 x plist1 plist2 =
  let elist = ref [] in
  let eone = ref [] in
  let x' = Exp.Var x in
  for i = 0 to List.length plist1 - 1 do
    let (t,u) = List.nth plist1 i in
    let a = mkExp_t t in
    let b = mkExp_t u in
    eone := [a <^= x'; x' <^= b];
    for j = 0 to List.length plist2 - 1 do
      let (p,q) = List.nth plist2 j in
      let c = mkExp_t p in
      let d = mkExp_t q in
      eone := ((x' <^< c) |^| (d <^< x')) :: !eone;
    done;
    elist := (bigAnd' !eone) :: !elist;
  done;
  let e = ex' [x] (bigOr' !elist) in
  e
;;

let phi_core vars (ss1: SHspat.t) (ss2 : SHspat.t) = 
  let x = genFreshVar "_x" vars in
  let rec mkPlist ss1 =
    match ss1 with
    | [] -> []
    | S.Pto(t,_)::ss2 -> (t,t)::(mkPlist ss2)
    | S.Arr(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Str(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Ind(_,tt)::ss2 -> (mkPlist ss2)
  in
  let plist1 = mkPlist ss1 in
  let plist2 = mkPlist ss2 in
  phi_1 x plist1 plist2
;;

let phi (sh1 : QFSH.t) (sh2 : QFSH.t) =
  let (_,ss1) = sh1 in
  let (_,ss2) = sh2 in
  let vars = (QFSH.fv sh1) @ (QFSH.fv sh2) in
  phi_core vars ss1 ss2
;;

(* making rho1 *)
(* rho1 sh1 sh2 <-> "there exist Arr(t1,t2) in sh1 and Str(u1,u2) in sh2 such that (t1,t2) comm (u1,u2)" *)
let rho1 sh1 sh2 =
  let ss1 = snd sh1 in
  let ss2 = snd sh2 in
  let _ee = ref [] in
  let segArr = SS.getArraySeg ss1 in
  let segStr = SS.getStringSeg ss2 in
  for i = 0 to List.length segArr - 1 do
    for j = 0 to List.length segStr - 1 do
      let (t1,t2) = List.nth segArr i in
      let d1 = mkExp_t t1 in
      let d2 = mkExp_t t2 in
      let (u1,u2) = List.nth segStr j in
      let e1 = mkExp_t u1 in
      let e2 = mkExp_t u2 in
      _ee := ((e1 <^= d2) &^& (d1 <^= e2)) :: !_ee
    done;
  done;
  bigOr' !_ee
;;

(* making rho2 *)
(* rho2 sh1 sh2 <-> "there exist t->(0) in sh1 and Str(u1,u2) in sh2 such that u1 <= t <= u2 " *)
let rho2 sh1 sh2 = 
  let ss1 = snd sh1 in
  let ss2 = snd sh2 in
  let _ee = ref [] in
  let extract_ptozero s =
    match s with
    | S.Pto(t,[(_,u)]) when u = zero -> [t]
    | _ -> []
  in
  let tt = List.flatten @@ List.map extract_ptozero ss1 in
  let segStr = SS.getStringSeg ss2 in
  for i = 0 to List.length tt - 1 do
    for j = 0 to List.length segStr - 1 do
      let t = List.nth tt i in
      let e = mkExp_t t in
      let (u1,u2) = List.nth segStr j in
      let e1 = mkExp_t u1 in
      let e2 = mkExp_t u2 in
      _ee := ((e1 <^= e) &^& (e <^= e2)) :: !_ee
    done;
  done;
  bigOr' !_ee
;;

(* making chi *)
let chi_1 (kA : QFSH.t) (kB : QFSH.t) =
  let notgammaB = not'(bigAnd' (Satcheck.gammaExp_sh kB)) in (* kB has no heap with the current store *)
  let phiAB = phi kA kB in (* there is a cell that is covered by kA, but is not covered by kB *)
  let phiBA = phi kB kA in (* there is a cell that is covered by kB, but is not covered by kA *)
  let psiAB1 = psi1 kA kB in (* there exist Arr/Str(a,b) in kA and d->_ in kB such that a <= d <= b *)
  let psiAB2 = psi2 kA kB in (* there exist t->cc1 in kA and t->cc2 in kb such that cc1 <> cc2 *)
  let rhoAB1 = rho1 kA kB in (* there exist Arr(a,b) in kA and Str(a',b') in kb such that (a,b) comm (a',b') *)
  let rhoAB2 = rho2 kA kB in (* there exist a->(0) in kA and Str(a',b') in kb such that a' <= a <= b' *)
  bigOr' [notgammaB;phiAB;phiBA;psiAB1;psiAB2;rhoAB1;rhoAB2]
;;

let chi kA kkB =
  let gammaA = Satcheck.gammaExp_sh kA in
  let ee = List.map (chi_1 kA) kkB in
  bigAnd' (gammaA @ ee)
;;

let entlcheck (entl : QFEntl.t) =
  let (k,kk) = entl in
  let exp = chi k kk in
  match checkSatExp ~modelflag:false ~ucflag:false exp with 
  | SatResult.Model _ -> false
  | SatResult.UnsatCore _ -> true
  | SatResult.Unknown -> print_endline "entlcheck: Unknown"; failwith ""
;;

(* reduceEntlPure [p1;p2;p3] (k,kk) *)
(* Original form: p1 & p2 & p3 & k |- kk (valid entailment) *)
(* It drops p1 if p2 & p3 & k |- kk is still valid *)
(* Repeat this as long as it is a valid entailment *)
let reduceQFEntlPure (pp,entl) =
  let (k,kk) = entl in
  let (p0,ss0) = k in
  let _tmpPP = ref pp in
  let _prePP = ref [] in
  while !_tmpPP <> !_prePP do
    _prePP := !_tmpPP;
    try
      for i = 0 to List.length !_tmpPP - 1 do
        let (p1,pp1) = List_tailrec.takeNth !_tmpPP i in
        let k' = (P.And (p0::pp1),ss0) in
        match entlcheck (k',kk) with
        | true -> _tmpPP := pp1; raise Skip
        | false -> ()
      done;
    with
      Skip -> ()
  done;
  (!_tmpPP,entl)
;;

let reduceQFEntlTest entl =
  let ((p,ss),kk) = entl in
  match p with
  | P.And pp ->
     let entl1 = ((P.True,ss),kk) in
     let (pp1,_) = reduceQFEntlPure (pp,entl1) in
     begin
       match pp1 with
       | [] -> ((P.True,ss),kk)
       | p2::[] -> ((p2,ss),kk)
       | _ -> ((P.And pp1,ss),kk)
     end
  | _ -> entl
;;

let simplifyPureL pp =
  let p = Sltosmt.simplifyPure (P.And pp) in
  P.flatten "and" p
;;  

(* Simpler version *)
let reduceQFEntlPure_simpl (pp,entl) =
  let pp1 = simplifyPureL pp in
  (pp1,entl)
;;
    
let decide_ps (ps : PS.t) =
  let result = ref true in
  begin
  try
    for i = 0 to (List.length ps) - 1 do
      if entlcheck (QFEntl.down (List.nth ps i))
      then ()
      else
	    raise Exit (* An invalid entailment is found *)
    done;
  with
    Exit -> result := false 
  end;
  !result
;;
