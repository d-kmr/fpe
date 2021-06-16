(*
  Satchecker of symbolic heaps
*)

open Tools
open Slsyntax
open Sltosmt
open Smtsyntax
open Smttoz3
module SatResult = Smttoz3.SatcheckResult
   
(* brotherston's gamma *)
(* gamma (t->_ * Arr(a,b) * Str(c,d)) is (a <= b & c <= d & t out [a,b] & t out [c,d] *)
let gamma ss : P.t list =
  let seg = List.map S.mkInterval ss in
  let condSeg = List.flatten @@ List.map (fun (t,u) -> [zero <.< t; t <.= u]) seg in
  let _res = ref condSeg in
  for i = 0 to List.length seg - 1 do
    for j = i+1 to List.length seg - 1 do
      let (ti,ui) = List.nth seg i in
      let (tj,uj) = List.nth seg j in
      _res := (_Disj ti ui tj uj) :: !_res
    done;
  done;
  !_res
;;

let gammaExp_sh sh : Exp.t list =
  let rec split_and p =
    match p with
    | P.And pp -> List.flatten (List.map split_and pp)
    | _ -> [p]
  in  
  let (p,ss) = sh in
  let pp = (split_and p) @ (gamma ss) in
  let ee = List.map mkExp_p pp in
  ee
;;


(* Satchecker with bignum *)
(* Assumptions *)
(* 1. hat variables have their id-numbers like x10@hat, x34@hat,.. *)
(* 2. A big number M (= 2^64*1000) is used for memory space of each hat-var *)
let mkSH_bn (sh : QFSH.t) =
  let bigNum2_10 = num 1000 in
  let bigNum2_4 = num 16 in  
  let bigNum2_64 = bigNum2_10 *.* bigNum2_10 *.* bigNum2_10 *.* bigNum2_10 *.* bigNum2_10 *.* bigNum2_10 *.* bigNum2_4 in
  let bigNum = bigNum2_64 *.* (num 100) in
  let (p,ss) = sh in
  let ttHatVars = union (P.hatVars p) (SS.hatVars ss) in
  let ttHatVars_sorted =
    let order t1 t2 =
      match t1,t2 with
      | T.Var (v1,_),T.Var (v2,_) when v1 > v2 -> 1
      | T.Var (v1,_),T.Var (v2,_) when v1 < v2 -> -1
      | _,_ -> 0
    in
    List.sort order ttHatVars
  in
  let hash = let tt = ttHatVars_sorted in zipLst (genLst (List.length tt)) tt in
  let mkPureOne (i,tHatVar) =
    let c = (num (i+1)) *.* bigNum in
    tHatVar =.= c
  in
  let pp1 = List.map mkPureOne hash in
  let p1 = P.And (p::pp1) in
  (p1,ss)
;;  

(* satchecker for Array with bignum *)
let satcheckArr_bn ~modelflag ~ucflag ~bnflag (sh : QFSH.t) =
  let sh1 = if bnflag then mkSH_bn sh else sh in
  checkSatExpL modelflag ucflag (gammaExp_sh sh1)
;;

(***************************)
(* Satchecker for Ls + Arr *)
(***************************)
let lsElim (k : QFSH.t) : QFSH.t list =
  let (p,ss) = k in
  let _res = ref [([p],[])] in
  let extend pp1 ss1 (pp2,ss2) = (pp1 @ pp2, ss1 @ ss2) in
  for i = 0 to List.length ss - 1 do
    match List.nth ss i with
    | S.Ind("Ls",t::u::_) ->
       let res1 = List.map (extend [t =.= u] []) !_res in
       let res2 = List.map (extend [t <.> u] [t -.> [("*",u)]]) !_res in
       _res := res1 @ res2
    | s ->
       _res := List.map (extend [] [s]) !_res
  done;
  List.map (fun (pp,ss) -> (P.And (List.rev pp), List.rev ss)) !_res
;;  

(* satchecker for Array+Ls with bignum *)
let satcheck_bn ~modelflag ~ucflag ~bnflag (sh :QFSH.t) : SatResult.t =
  let _ucL = ref [] in
  let _result = ref SatResult.Unknown in
  (* Presburger checking *)
  QFSH.checkPresburger sh;
    (* begin *)
  let _shL = ref (lsElim sh) in
  begin
    try
      while !_shL <> [] do
        let sh1 = List.hd !_shL in
        let bnflag = true in
        (* QFSH.println sh1; *)
        _shL := List.tl !_shL;
        match satcheckArr_bn modelflag ucflag bnflag sh1 with
        | SatResult.Model _ as q -> _result := q; raise Exit (* sat *)
        | SatResult.UnsatCore uc -> _ucL := uc @ !_ucL
        | SatResult.Unknown as q -> _result := q; raise Exit
      done;
      _result := SatResult.UnsatCore !_ucL
    with
      Exit -> ()
  end;
  !_result
;;
