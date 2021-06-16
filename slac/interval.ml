open Tools
open Slsyntax
open Satcheck
open Sltosmt
open Smtsyntax
open Smttoz3
module SatResult = Smttoz3.SatcheckResult
;;
   
module L = List

(* For debugging *)                 
let _debug = ref false
;;
let doifDebug f arg = if !_debug then f arg else ()
;;
let sayifDebug mes =
  let f () = print_endline mes in
  doifDebug f ()
;;
let _simplFlag = ref true
;;
let unset_simpl () = _simplFlag := false
;;

exception NoAnswer

(* Terminology 
Interval: an interval (l,u)

Segment: a set of disjoint intervals

Group:
- a set of intervals with left- and right-endpts
- any two intervals of it are connected
(I,I' are connected in G 
<-> I=I1,I2,..,Ik=I' in G, 
    and Ij and I(j+1) has a common element)

Partitions: a set of groups
*)

(*---------------------------------------*)
(* Common tools                          *)
(*---------------------------------------*)
module UnionCond = struct
  (* Condition for union *)
  type t = SHpure.t list
         
  let to_string (pp : t) = P.to_string (P.And pp)
    
  let print pp = print_string (to_string pp)
               
  let println pp = print_endline (to_string pp)
    
end
;;        
module Valuation = struct
  (* 'rho' is used *)
  type t = (SHterm.t * int) list
         
  let lookup (rho : t) t =
    try
      L.assoc t rho
    with
      Not_found -> -1
    
end
;;

let maxValue (rho : Valuation.t) (jj : Segments.t) =
  let module V = Valuation in
  let _max = ref [] in
  for i = 0 to L.length jj - 1 do
    let n = V.lookup rho (Invl.right (L.nth jj i)) in
    match !_max with
    | [] -> _max := [n]
    | m::_ ->
       if m < n then _max := [n] else ()
  done;
  if !_max = [] then -1 else L.hd !_max

let minValue (rho : Valuation.t) (jj : Segments.t) =
  let module V = Valuation in
  let _min = ref [] in
  for i = 0 to L.length jj - 1 do
    let n = V.lookup rho (Invl.left (L.nth jj i)) in
    match !_min with
    | [] -> _min := [n]
    | m::_ ->
       if n < m then _min := [n] else ()
  done;
  if !_min = [] then -1 else L.hd !_min
;;
           
module Group = struct
  (* 'g' is used *)
  (* ([(a,b);(c,d);(e,f)],2,0) is a group with left-ep 'e' and right-ep 'b' *)
  (* It will be (e,b) after merge *)
  type t = Invl.t list * int * int

  let create jj idxL idxR : t = (jj,idxL,idxR)
         
  let init jj : t = (jj,-1,-1)
         
  let endpoints (g : t) =
    let (jj,k0,k1) = g in
    let (t0,_) = List.nth jj k0 in
    let (_,t1) = List.nth jj k1 in
    (t0,t1)

  let body (g : t) = fst3 g

  (* ([(c1,d1),..,(cn,dn)],L,R) produces *)
  (* /\_i (ci = cL or \/_j cj < ci <= dj) and /\_i (di = dR or \/_j cj <= di < dj or \/_j di+1 = cj) *)
  let mergeCond (g : t) : UnionCond.t =
    let (cL,dR) = endpoints g in
    let tt = body g in
    let genL (ci,_) =
      let disjL1 = ci =.= cL in
      let disjL2 = L.map (fun (c,d) -> P.And [c <.< ci; ci <.= d +.+ one]) tt in
      P.Or (disjL1 :: disjL2)
    in
    let genR (_,di) =
      let disjR1 = di =.= dR in
      let disjR2 = L.map (fun (cj,dj) -> P.And [cj <.= di; di <.< dj]) tt in
      let disjR3 = L.map (fun (cj,_) -> di +.+ one =.= cj) tt in
      P.Or (disjR1 :: disjR2 @ disjR3)
    in
    (cL <.= dR) :: (L.map genL tt) @ (L.map genR tt)

  let merge (g : t) : Invl.t * UnionCond.t =
    (endpoints g, mergeCond g)

  let to_string (g : t) =
    let (t0,t1) = endpoints g in
    let jj = body g in
    let t0' = SHterm.to_string t0 in
    let t1' = SHterm.to_string t1 in
    let body = string_of_list Invl.to_string "," jj in
    "[" ^ body ^ "]@(" ^ t0' ^ "," ^ t1' ^ ")"

  let print g = print_string (to_string g)
              
  let println g = print_endline (to_string g)

end
;;
module Grp = Group
;;
module Partition = struct
  (* 'gg' is used *)
  type t = Group.t list

  let merge (gg : t) : Seg.t * UnionCond.t =
    let mg = L.map Grp.merge gg in
    let seg = L.map fst mg in
    (* condConnGrp: each group is connected *)
    let condConnGrp = L.flatten (L.map snd mg) in
    (* condDisjGrp: any two groups are strongly disjoint (not adjcent) *)
    let condDisjGrp =
      let _ans = ref [] in
      for i = 0 to L.length seg - 1 do
        for j = i+1 to L.length seg - 1 do
          let (ci,di) = L.nth seg i in
          let (cj,dj) = L.nth seg j in
          _ans := P.Atom (P.Disj, [ci;di;cj;dj]) :: !_ans
        done;
      done;
      !_ans
    in
    (seg, condConnGrp @ condDisjGrp)

end
;;                  
(*---------------------------------------*)
(* Implementation 1                      *)
(* Simpler Calculation of Union Interval *)
(* It's the same way as the biabduction  *)
(*---------------------------------------*)
module ColoredArray = struct
  (* 'a' is an array of colors (true:colored,false:uncolored) *)
  (* 'b' is an array of endpoint lists. *)
  (* a[0] and a[N+1] must be false (1,..,N is used) *)
  (* the last cell is an sentinel (always false or []) *)
  (* [|f ;t        ;t        ;t ;t        ;t        ;f |] *)
  (* [|[];[(a,0,L)];[(b,1,L)];[];[(c,0,R)];[(d,1,R)];[]|] *)
  (* means overlapped intervals (a,c) and (b,d) *)
  type arrayA = bool array
  type cell = (Slsyntax.SHterm.t * int * string) list
  type arrayB = cell array
  type t = arrayA * arrayB

  let init n : t =
    let a = Array.make (n+2) false in
    let b = Array.make (n+2) [] in
    (a,b)
    
end
;;
                    
let mkColoredArray (rho : Valuation.t) (jj : Seg.t) : ColoredArray.t =
  let order (t1,idx1,pos1) (t2,idx2,pos2) =
    match pos1,pos2,idx1>idx2 with
    | "R","L",_ -> 1
    | "L","R",_ -> -1
    | _,_,true -> 1
    | _,_,false -> -1
  in  
  let max = maxValue rho jj in
  let (a,b) = ColoredArray.init max in
  for i = 0 to L.length jj - 1 do
    let t0 = Invl.left (L.nth jj i) in
    let t1 = Invl.right (L.nth jj i) in
    let n0 = Valuation.lookup rho t0 in
    let n1 = Valuation.lookup rho t1 in
    Array.set b n0 ((t0,i,"L")::(Array.get b n0));
    Array.set b n1 ((t1,i,"R")::(Array.get b n1));
    for k = n0 to n1 do
      Array.set a k true
    done;
  done;
  for i = 0 to Array.length b - 1 do
    let tri = Array.get b i in
    Array.set b i (List.sort order tri)
  done;
  (a,b)

(* merge [(x,4);(y,7);(a,6);(b,9)] [(x,y);(a,b)] *)
(* returns [(x,b)] and [|-;(x,0,L);...;(b,1,R);-|] *)
let merge (rho : Valuation.t) (jj : Segments.t) : Seg.t * ColoredArray.arrayB =
  let fst3 (x,_,_) = x in
  let (a,b) = mkColoredArray rho jj in
  let _left = ref [] in
  let _res = ref [] in
  for i = 0 to Array.length a - 2 do
    let cur = Array.get a i in
    let next = Array.get a (i+1) in
    match cur,next with
    | true,false -> (* cur:right-endpoint *)
       let t0 = L.hd !_left in
       let rends = L.map fst3 (L.filter (fun (_,_,lr) -> lr="R") (Array.get b i)) in
       let t1 = L.hd (L.rev rends) in
       _left := [];
       _res := (t0,t1) :: !_res
    | false,true -> (* next:left-endpoint *)
       let lends = L.map fst3 (L.filter (fun (_,_,lr) -> lr="L") (Array.get b (i+1))) in
       _left := lends;
    | _,_ -> ()
  done;
  (L.rev !_res,b)

let mkBlock (b : ColoredArray.arrayB) : ColoredArray.cell list =
  let _close = ref 0 in
  let _tmp = ref [] in
  let _res = ref [] in
  for k = 0 to Array.length b - 1 do
    let cell = Array.get b k in
    for j = 0 to List.length cell - 1 do
      let (t,idx,pos) = (List.nth cell j) in
      _tmp := (t,idx,pos) :: !_tmp;
      match pos with
      | "L" -> _close := !_close + 1
      | "R" -> _close := !_close - 1
      | _ -> ()
    done;
    if cell <> [] && !_close = 0
    then
      begin
        _res := (List.rev !_tmp) :: !_res;
        _tmp := []
      end
    else ()
  done;
  List.rev !_res

let mkCondition (blk : ColoredArray.cell list) : UnionCond.t =
  let blkhd b = fst3 (List.hd b) in
  let blklast b = fst3 (List.nth b (List.length b - 1)) in
  let _conj1 = ref [] in
  (* making block-inner condition *)
  for i = 0 to List.length blk - 1 do
    let b = List.nth blk i in
    let _t = ref (fst3 (List.hd b)) in
    for j = 1 to List.length b - 1 do
      let (u,_,_) = List.nth b j in
      _conj1 := (!_t <.= u) :: !_conj1;
      _t := u
    done;
  done;
  (* making block-outer condition *)
  let _conj2 = ref [] in 
  for i = 0 to List.length blk - 1 do
    let bi = List.nth blk i in
    let ti,ui = blkhd bi, blklast bi in
    for j = i+1 to List.length blk - 1 do
      let bj = List.nth blk i in
      let tj,uj = blkhd bj, blklast bj in
      _conj2 := P.Atom (P.Disj,[ti;ui;tj;uj]) :: !_conj2
    done;
  done;
  !_conj1 @ !_conj2

(* Union Interval: the main function of implementation 1 *)
let unionInterval1 (cond : SHpure.t) (jj : Seg.t) : Seg.t * UnionCond.t = 
  (* Example seg = [ (t1,u1);(t2,u2) ] *)
  let seg_pp =   (* it's [ [0<p1<=q1;0<p2<=q2] ] in DNF *)
    L.flatten (L.map (fun (t0,t1) -> [zero <.< t0;t0 <.= t1]) jj)
  in
  let exp_cond = mkExp_p cond in
  let exp_seg = List.map mkExp_p seg_pp in
  let exp = bigAnd' (exp_cond :: exp_seg) in
  match checkSatExp ~modelflag:true ~ucflag:false exp with
  | SatResult.Model varvalbnL ->
     let varvalL = List.map (fun (v,bn) -> (v,Bignum.to_int bn)) varvalbnL in
     let endpoints = L.flatten (L.map (fun (t0,t1) -> [t0;t1]) jj) in
     let rho =
       L.map
         (fun t -> (t,SHterm.evalUnderPmodel varvalL t))
         endpoints
     in
     let (jj1,b) = merge rho jj in
     let cond = mkCondition (mkBlock b) in
     (jj1,cond)
  | _ -> raise NoAnswer
;;
(*---------------------------------------*)
(* Implementation 2                      *)
(* Calculation of All Union Intervals    *)
(* good: all possibilities are listed    *)     
(* bad: exp order                        *)
(*---------------------------------------*)
type preGroup = Invl.t list
type prePartition = preGroup list
     
(* insertToNth [[a];[b];[c]] d 1 is  [[a];[d;b];[c]]   *)
(* insertToNth [[a];[b];[c]] d 3 is  [[a];[b];[c];[d]] *)
let insertToNth xxx x n =
  let rec aux xxx0 xxx1 k =
    match xxx1,k with
    | [],_ -> List_tailrec.append_rev xxx0 [[x]]
    | xx::xxx1',0 -> List_tailrec.append_rev xxx0 ((x::xx)::xxx1')
    | xx::xxx1',_ -> aux (xx::xxx0) xxx1' (k-1)
  in
  aux [] xxx n
;;
(* Producing all partitions *)
(* mkAllPartitions [1;2] returns [[1;2]], [[1];[2]] *)
let mkAllPrePartitions (xx : Seg.t) : prePartition list = 
  let _ans = ref [[]] in
  let _tmp = ref [] in
  for k = 0 to L.length xx - 1 do
    let x = L.nth xx k in
    for i = 0 to L.length !_ans - 1 do
      let xxx = L.nth !_ans i in
      for j = 0 to L.length xxx do
        _tmp := (insertToNth xxx x j) :: !_tmp;
      done;
    done;
    _ans := !_tmp;
    _tmp := [];
  done;
  !_ans
;;
let groupCasesFromPreGroup (jj : preGroup) : Grp.t list =
  let _ans = ref [] in
  let _epL = ref [] in
  for idxL = 0 to L.length jj - 1 do
    let t = fst (L.nth jj idxL) in
    match L.mem t !_epL with
    | true -> ()
    | false -> 
       _epL := t :: !_epL;
       for idxR = 0 to L.length jj - 1 do
         _ans := (Grp.create jj idxL idxR) :: !_ans;
       done;
  done;
  !_ans
;;      
let partitionCasesFromPrePartition (jjj : prePartition) : Partition.t list =
  let _ans = ref [[]] in
  let _tmp = ref [] in
  for k = 0 to L.length jjj - 1 do
    let jj = L.nth jjj k in
    let gg = groupCasesFromPreGroup jj in
    for l = 0 to L.length !_ans - 1 do
      let part = L.nth !_ans l in
      _tmp := (List_tailrec.map (fun g -> g::part) gg) @ !_tmp
    done;
    _ans := !_tmp;
    _tmp := [];
  done;
  !_ans
;;      

(* generate all partitions from a given segment *)
let mkAllPartitions (xx : Seg.t) : Partition.t list = 
  let jjjj = mkAllPrePartitions xx in
  L.flatten (L.map partitionCasesFromPrePartition jjjj)
;;

(*-----------------------------------------------------------
Union Interval: the main function of implementation 2
'cond' is a given condition
------------------------------------------------------------*)
let unionInterval2 (cond : SHpure.t) (jj : Seg.t) =
  Seg.checkPresburger jj;
  let showmodel model =
    L.iter (fun (v,bn) -> print_string @@ "(" ^ v ^ "," ^ (Bignum.to_string bn) ^ ") ") model;
    print_endline "\n"
  in
  let basiccond = L.flatten @@ L.map (fun (t,u) -> [zero <.< t; t <.= u]) jj in  
  let gg = mkAllPartitions jj in
  let _ans = ref [] in
  let _cond = ref P.True in
  for i = 0 to L.length gg - 1 do
    let g = L.nth gg i in
    let (seg,unioncond) = Partition.merge g in
    doifDebug print_endline "Produced segment (raw)";
    doifDebug Seg.println seg;
    
    _cond := P.And (cond :: basiccond @ unioncond);
    if !_simplFlag then
        _cond := simplifyPure !_cond
    else ();
    doifDebug print_endline "Produced condition";
    doifDebug UnionCond.println [!_cond];
    
    doifDebug print_endline "Checking Condition ...";
    let exp_cond = mkExp_p !_cond in
    match checkSatExp ~modelflag:true ~ucflag:false exp_cond with
    | SatResult.Model model ->
       Ftools.pf_s "INTERVAL" showmodel model;
       _ans := (seg,!_cond) :: !_ans
    | SatResult.UnsatCore _ ->
       Ftools.pf_s "INTERVAL" print_endline "unsat\n";
       ()
    | SatResult.Unknown ->
       Ftools.pf_s "INTERVAL" print_endline "unknown\n";
       ()
  done;
  !_ans
;;




(*-----------------------------------------------------------
Max Interval
'cond' is a given condition
Note: cond is a pure formula
maxInterval cond [(a1,b1);(a2,b2);(a3,b3)] produces
[
( (a1,b1), a1<=b1 & a2<=b2 & a3<=b3 & b2<=b1 & b3<=b1 & a1 <= a2 & a1 <= a3);
( (a3,b2), a1<=b1 & a2<=b2 & a3<=b3 & b1<=b2 & b3<=b2 & a3 <= a1 & a3 <= a2);
( (a1,b3), a1<=b1 & a2<=b2 & a3<=b3 & b1<=b3 & b2<=b3 & a1 <= a2 & a1 <= a3);
]
------------------------------------------------------------*)
let mkAllMinConds (jj : Seg.t) = 
  let lEndPts = List.map (fun (p,_)->p) jj in
  let _res = ref [] in
  for i = 0 to List.length lEndPts - 1 do
    let (rMin,eps) = List_tailrec.takeNth lEndPts i in
    let pp = List.map (fun r -> rMin <.= r) eps in
    _res := (rMin,pp) :: !_res
  done;
  !_res
;;

let mkAllMaxConds (jj : Seg.t) = 
  let rEndPts = List.map (fun (_,p)->p) jj in
  let _res = ref [] in
  for i = 0 to List.length rEndPts - 1 do
    let (rMax,eps) = List_tailrec.takeNth rEndPts i in
    let pp = List.map (fun r -> r <.= rMax) eps in
    _res := (rMax,pp) :: !_res
  done;
  !_res
;;


let maxInterval (cond : SHpure.t) (jj : Seg.t) : (Invl.t * SHpure.t) list =
  Seg.checkPresburger jj;
  let showmodel model =
    L.iter (fun (v,bn) -> print_string @@ "(" ^ v ^ "," ^ (Bignum.to_string bn) ^ ") ") model;
    print_endline "\n"
  in
  let basiccond = L.flatten @@ L.map (fun (t,u) -> [zero <.< t; t <.= u]) jj in
  let minConds = mkAllMinConds jj in  
  let maxConds = mkAllMaxConds jj in
  let _ans = ref [] in
  let _cond = ref P.True in
  for i = 0 to L.length minConds - 1 do
    for j = 0 to L.length maxConds - 1 do
      let (rMin,leftmostcond) = L.nth minConds i in
      let (rMax,rightmostcond) = L.nth maxConds j in
      
      _cond := P.And (cond :: basiccond @ leftmostcond @ rightmostcond);
      if !_simplFlag then
          _cond := simplifyPure !_cond
      else ();
      doifDebug print_endline "Produced condition";
      doifDebug UnionCond.println [!_cond];
      
      let exp_cond = mkExp_p !_cond in
      let maxInvl = (rMin,rMax) in
      Ftools.pf_s "INTERVAL" print_endline "Produced max-interval";
      Ftools.pf_s "INTERVAL" Invl.println maxInvl;
      Ftools.pf_s "INTERVAL" print_endline "Checking Condition ...";
      match checkSatExp ~modelflag:true ~ucflag:false exp_cond with
      | SatResult.Model model ->
         Ftools.pf_s "INTERVAL" showmodel model;
         _ans := (maxInvl,!_cond) :: !_ans
      | SatResult.UnsatCore _ ->
         Ftools.pf_s "INTERVAL" print_endline "unsat\n";
         ()
      | SatResult.Unknown ->
         Ftools.pf_s "INTERVAL" print_endline "unknown\n";
         ()
    done;
  done;
  !_ans
;;
