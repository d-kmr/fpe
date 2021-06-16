open Tools
open Slsyntax
open Sltosmt   
open Smttoz3
open Smtsyntax
module SatResult = Smttoz3.SatcheckResult
  
(* tag for debugging: -deb "BIABD_debug" *)
let tagDebug = "BIABD_debug"
;;
let tagTime = "BIABD_time"
;;
(* Grouping flag *)
(* true : do biabduction with grouping (several answers but possibly slow) *)
(* false : do biabduction without grouping (one answer but quick) *)
let grpFlag = ref true
;;
let unset_grouping () = grpFlag := false
;;
let setGrp () = grpFlag := true
;;
let (tm1,tm2) = (ref 0.0,ref 0.0)
;;
let getTime1 () = tm1 := Sys.time ()
;;
let getTime2 () = tm2 := Sys.time ()
;;
let showTimeDiff mes = print_endline (mes ^ " (" ^ (string_of_float (!tm2 -. !tm1)) ^ ")")
;;
(* Simplification flag *)
(* true : do biabd with simplification of pure part *)
(* false : do biabd without simplification of pure part *)
let simplFlag = ref true
;;
let unset_simpl () = simplFlag := false
;;

(* Debugging flag *)
let debugFlag = ref false
;;
let unsetDebug () = debugFlag := false
;;
let setDebug () = debugFlag := true
;;
let doIfDebug f x = if !debugFlag then f x else ()
;;
let sayIfDebugLazy fmes = if !debugFlag then print_endline (fmes ()) else ()
;;

let show_pmodel pmodel =
  let show_one (v,n) = prerr_endline @@ v ^ " = " ^ (string_of_int n) in
  List.iter show_one pmodel
;;

let isValid_pb p =
  let vv = P.fv p in
  let q = all' vv (mkExp_p p) in
  checkSatExpBool q
;;

(* Pure extraction from QFSH *)
let extractPureSS ss : P.t list =
  let _pp = ref [] in
  let rec mkPlist ss1 =
    match ss1 with
    | [] -> []
    | S.Pto(t,_)::ss2 -> (t,t)::(mkPlist ss2)
    | S.Arr(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Str(t,u)::ss2 -> (t,u)::(mkPlist ss2)
    | S.Ind(_,_)::ss2 -> (mkPlist ss2)
  in
  let plist = mkPlist ss in
  for i = 0 to List.length plist - 1 do
    for j = i+1 to List.length plist - 1 do
      let (ti,ui) = List.nth plist i in
      let (tj,uj) = List.nth plist j in
      match ti = ui, tj = uj with
      | true,true ->
         _pp := (ti <.> tj) :: !_pp
      | true,false ->
         _pp := (_Out ti tj uj) :: !_pp
      | false,true ->
         _pp := (_Out tj ti ui) :: !_pp
      | _,_ ->
         _pp := (_Disj ti ui tj uj) :: !_pp
    done;
  done;  
  !_pp
;;
let extractPureSH (k : QFSH.t) =
  let (p,ss) = k in
  let pp = extractPureSS ss in
  p::pp
;;

(* checking quasi-equivalence (in some sense) of two SHs *)
let checkQuasiEquivSH k1 k2 =
  let p1 = P.And (extractPureSH k1) in
  let p2 = P.And (extractPureSH k2) in
  let vv = union (P.fv p1) (P.fv p2) in
  let e1 = mkExp_p p1 in
  let e2 = mkExp_p p2 in
  let e = all' vv ((e1 -^> e2) &^& (e2 -^> e1)) in
  checkSatExpBool e
;;

module Group = struct
  (* A group: (block_terms, spat1, spat2) *)
  (* 'g' is used *)
  (* A group means a memory block of the same type *)
  (* terms in block_terms belong in the block *)
  (* [t;a@hat] means that t and ""terms that contains a@hat"" are in the block *)
  (* - b@hat/b@dot/b@tilde cannot be in the block of a@hat *)
  (* - b@bar may be in the block of a@hat *)
  type t = 
    {
      mutable gid : int; (* id of the Groups to which the group belongs *)
      mutable id : int; (* id of the group in the belonging Groups *)
      mutable blktm : T.t list; (* block term: hat,dot,tilde,check-vars + address terms *)
      mutable ss1 : S.t list;
      mutable ss2 : S.t list
    }

  let create tt ss1 ss2 = 
    {
      gid = 0; (* dummy *)
      id = 0; (* dummy *)
      blktm = tt;
      ss1 = ss1;
      ss2 = ss2;
    }

  let to_string (g : t) =
    let tt' = string_of_list T.to_string "," g.blktm in
    let ss1' = SS.to_string g.ss1 in
    let ss2' = SS.to_string g.ss2 in
    let gid' = string_of_int g.gid in
    let id' = string_of_int g.id in
    let header = "G_" ^ gid' ^ "_" ^ id' ^ ": " in
    header ^ "blktm=[" ^ tt' ^ "], ss1=[" ^ ss1' ^ "], ss2=[" ^ ss2' ^ "]"
                                                                   
  let println (g : t) = print_endline (to_string g)
                         
end
;;

module Groups = struct    

  type t =
    {
      mutable id : int;
      body : Group.t list
    }
    
  (* '_G' is used *)

  let create ggid ggbody = { id = ggid; body = ggbody }
    
  let push g _G =
    {
      id = _G.id;
      body = g :: _G.body
    }
    
  let length _G = List.length (_G.body)

  let nth _G i = List.nth _G.body i

  let refreshId _G =
    for i = 0 to List.length _G.body - 1 do
      let g = List.nth _G.body i in
      g.Group.gid <- _G.id;
      g.Group.id <- i
    done
                
  let to_string (_G : t) =
    let body = string_of_list Group.to_string "\n" _G.body in
    "---\n" ^ body 
                        
  let println (_G : t) = print_endline (to_string _G)
                      
end
;;

module GG = struct

  type t = Groups.t list
  (* _GG is used *)

  let refreshId (_GG : t) =
    for i = 0 to List.length _GG - 1 do
      let _G = List.nth _GG i in
      _G.Groups.id <- i;
      Groups.refreshId _G
    done
         
  let println (_GG : t) = List.iter Groups.println _GG

end
;;

module BAquery = struct
  (* Biabduction query *)
  (* (gid,pure_ex,pure,ss1,ss2) *)
  type t = string * P.t list * P.t * SS.t * SS.t

  let to_string (bq : t) =
    let (gid, pp_ex,p,ss1,ss2) = bq in
    let ss1' = SS.to_string ss1 in
    let ss2' = SS.to_string ss2 in
    match pp_ex,p with
    | [],P.True ->
       ss1' ^ " * X |- " ^ ss2' ^ " * Y "
    | [],_ ->
       let p' = P.to_string p in
       p' ^ " && " ^ ss1' ^ " * X |- " ^ ss2' ^ " * Y "
    | _,P.True ->
       let pex' = P.to_string (P.And pp_ex) in
       pex' ^ " && " ^ ss1' ^ " * X |- " ^ ss2' ^ " * Y "
    | _,_ ->
       let p' = P.to_string p in
       let pex' = P.to_string (P.And pp_ex) in
       pex' ^ " & " ^ p' ^ " && " ^ ss1' ^ " * X |- " ^ ss2' ^ " * Y "       

  let println (bq : t) = prerr_endline (to_string bq)
       
end
;;

module BAanswer = struct
  (* Biabduction answer *)
  (* (id,pureL,ss1,ss2) *)
  type t =
    {
      mutable gid : string;
      mutable pp : P.t list;
      mutable ssX : SS.t;
      mutable ssY : SS.t
    }

  let create id pp ssX ssY =
    {
      gid = id;
      pp = pp;
      ssX = ssX;
      ssY = ssY;
    }

  let clone (ba : t) = create ba.gid ba.pp ba.ssX ba.ssY
    
  let to_string_head hd (ba : t) =
    let gid' =
      match ba.gid with
      | "" -> ""
      | _ -> "_" ^ ba.gid
    in
    let pp'  = P.to_string (P.And (ba.pp)) in
    let ssX' = SS.to_string ba.ssX in
    let ssY' = SS.to_string ba.ssY in
    let outP = "P" ^ gid' ^ ": " ^ pp' in
    let outX = "X" ^ gid' ^ ": " ^ ssX' in
    let outY = "Y" ^ gid' ^ ": " ^ ssY' in
    hd ^ outP ^ "\n" ^ hd ^ outX ^ "\n" ^ hd ^ outY

  let to_string ba = to_string_head "" ba
    
  let println_head hd (ba : t) = prerr_endline (to_string_head hd ba)
    
  let println ba  = println_head "" ba
                       
  let printlnln (ba : t) = print_endline (to_string ba); print_newline()

  (* Answer combining *)
  let combine (baL : t list) : t =
    let _gid = ref "" in
    let _pp = ref [] in
    let _ssX = ref [] in
    let _ssY = ref [] in                 
    for i = 0 to List.length baL - 1 do
      let ba = List.nth baL i in
      _gid := ba.gid ^ !_gid;
      _ssX := ba.ssX @ !_ssX;
      _ssY := ba.ssY @ !_ssY;
      _pp := ba.pp @ !_pp;
    done;
    create !_gid !_pp !_ssX !_ssY

  let combineL baL1 baL2 =
    let _baL = ref [] in
    for i = 0 to List.length baL1 - 1 do
      for j = 0 to List.length baL2 - 1 do
        let ba1 = List.nth baL1 i in
        let ba2 = List.nth baL2 j in
        _baL := (combine [ba1;ba2]) :: !_baL;
      done;
    done;
    !_baL
    
    
  (* Answer refinement *)
  let refine (bq : BAquery.t) (ba : t) =
    Ftools.pf_s tagTime print_endline "Start BAanswer.Refine";
    Ftools.pf_s tagTime getTime1 ();
    let (gid,pp_ex,p,ss1,ss2) = bq in
    let k1 = (P.And (p :: pp_ex), ss1 @ ba.ssX) in
    let k2 = (P.True, ss2@ba.ssY) in
    let entl = (k1,[k2]) in
    let (pp',_) = EntlcheckA.reduceQFEntlPure_simpl (ba.pp, entl) in
    let ba1 = clone ba in
    ba1.pp <- if pp' <> [] then pp' else [P.True];
    Ftools.pf_s tagTime getTime2 ();
    Ftools.pf_s tagTime showTimeDiff "End BAanswer.Refine";
    ba1
    
  (* Checking quasi-equality of two answers *)
  let checkQuasiEquality (bq : BAquery.t) ba1 ba2 =
    let (_,pp_ex,p,ss,_) = bq in
    let p1 = P.And (p :: pp_ex @ ba1.pp) in
    let ss1 = ss @ ba1.ssX in
    let k1 = (p1,ss1) in
    let p2 = P.And (p :: pp_ex @ ba2.pp) in
    let ss2 = ss @ ba2.ssX in
    let k2 = (p2,ss2) in    
    checkQuasiEquivSH k1 k2


  (* addContentsPure *)
(* Input
ss1: [ t->(f:x,g:y); 10->() ] 
ss2: [ t->(g:z+1,f:1) ] 
Result
x=1 & y=z+1
 *)
  let update_ptocontents bq ba =
    let (_,pp_ex,p,ss1,ss2) = bq in
    let p1 = P.And (p :: pp_ex @ ba.pp) in
    let ss1' = ss1 @ ba.ssX in
    let h : QFSH.t = (p1,ss1') in
    let _pmodel = ref [] in
    let setPModel () =
      match Satcheck.satcheck_bn ~modelflag:true ~ucflag:false ~bnflag:true h with
      | SatResult.Model pmod -> _pmodel := List.map (fun (v,bn)->(v,Bignum.to_int bn)) pmod
      | _ -> raise Exit
    in
    let mkSortedPto ss = (* t->(f:u1;g:u2) becomes [ (n,[(f:u1);(g:u2)]) ] *)
      let vcc = List.flatten @@
                  List.map
                    (fun s -> match s with S.Pto(t,cc) -> [(SHterm.evalUnderPmodel !_pmodel t,cc)] | _ -> [])
                    ss
      in
      List.sort (fun p1 p2 -> compare (fst p1) (fst p2)) vcc
    in
    let mkPairFromDic f dic1 dic2 = (* dic : a list with sorted indexes, like [ (1,"ABC"); (2,"XYS") ] *)
      let rec aux res d1 d2 =
        match d1,d2 with
        | [],_ | _,[] -> List.rev res
        | (k1,c1)::d1',(k2,c2)::d2' ->
           if k1 = k2 then aux ((f c1 c2)::res) d1' d2'
           else if k1 < k2 then aux res d1' d2
           else aux res d1 d2'
      in
      aux [] dic1 dic2
    in
    try
      setPModel ();
      let ccPairs = mkPairFromDic (fun x y -> (x,y)) (mkSortedPto ss1) (mkSortedPto ss2) in
      let ppContents =
        List.flatten @@ List.map (fun ccPair -> mkPairFromDic ( =.= ) (fst ccPair) (snd ccPair)) ccPairs
      in
      ba.pp <- ba.pp @ ppContents;
    with
      Exit -> ()

  let subst sub ans =
    ans.pp <- List.map (P.subst sub) ans.pp;
    ans.ssX <- SS.subst sub ans.ssX;
    ans.ssY <- SS.subst sub ans.ssY;
    ans

  let unfold_indirect ans =
    ans.ssX <- SS.unfold_indirect ans.ssX;
    ans.ssY <- SS.unfold_indirect ans.ssY;
    ans

end
;;

module BAoutput = struct
  (* Biabduction output: (baAnswerL,pp)  *)
  (* pp is unsat condition *)
  (* baAnswerL = [(id,pureL,ss1,ss2)] *)
  type t = BAanswer.t list * P.t list

  let to_string (ba_out : t) =
    let (baL,pp) = ba_out in
    match baL,pp with
    | [],[] -> "No Output"
    | _,[] ->
       let baLstr = string_of_list BAanswer.to_string "\n" baL in
       baLstr
    | _,_ ->
       let baLstr = string_of_list BAanswer.to_string "\n" baL in
       let ppStr = P.to_string (P.And pp) in
       baLstr ^ "\n" ^ ppStr
       

  let subst sub (ba_out : t) =
    let (baL,pp) = ba_out in
    let baL' = List.map (BAanswer.subst sub) baL in
    let pp' = List.map (P.subst sub) pp in
    (baL',pp')
    
  let print (ba_out : t) = print_string (to_string ba_out)

  let println (ba_out : t) = print_endline (to_string ba_out)                         

  let unfold_indirect ba_out =
    let (baL,pp) = ba_out in
    let baL' = List.map BAanswer.unfold_indirect baL in
    (baL',pp)
                           
end
;;

let baSatcheck pp_ex pure ss1 ss2 ba =
  let pA = P.And (ba.BAanswer.pp @ pp_ex @ [pure]) in
  let ssA = ba.BAanswer.ssX @ ss1 in
  let shA = (pA,ssA) in
  match Satcheck.satcheck_bn ~modelflag:true ~ucflag:false ~bnflag:true shA with
  | SatResult.Model _ -> ([ba],[])  (* sat *)
  | _ -> ([],[pA]) (* unsat *)
;;

let baSatcheckL pp_ex pure ss1 ss2 baL : BAoutput.t =
  let _pp = ref [] in
  let _baL = ref [] in
  for i = 0 to List.length baL - 1 do
    let ba = List.nth baL i in
    let (baL,pL) = baSatcheck pp_ex pure ss1 ss2 ba in
    _pp := pL @ !_pp;
    _baL := baL @ !_baL;
  done;
  (!_baL,!_pp)


(*-------------------------------------------------
Grouping: splitting a biabduction problem into several smaller biabduction problems 

Example: grouping True [a@hat -> [] ; Arr(x@bar,b@hat+10)] [y@bar -> [] ; Arr(a@hat,a@hat+1)]
This returns
--
group1a: ( [a@hat], a@hat->[],  Arr(a@hat,a@hat+1) )
group1b: ( [b@hat], Arr(x1@bar,b@hat+10), Emp )
group1c: ( [y@bar], Emp, y@bar->[] )
--
group2a: ( [a@hat,y@bar], a@hat->[],  y@bar->[] * Arr(a@hat,a@hat+1) )
group2b: ( [b@hat], Arr(x1@bar,b@hat+10), Emp )
--
group3a: ( [a@hat], a@hat->[],  Arr(a@hat,a@hat+1) )
group3b: ( [b@hat,y@bar], Arr(x1@bar,b@hat+10), y@bar->[] )
-------------------------------------------------*)
let mkClosure t =
  match T.getHeadTerm t with
  | t'::_ -> t' :: (T.hatVars' t')
  | _ -> []
;;
let mkClosureL tt = unionL (List.map mkClosure tt)
;;
let grouping pure ssA ssB : GG.t =
  let g_emp = Group.create [] [] [] in
  let isEmpGrp g = g.Group.blktm = [] && g.Group.ss1 = [] && g.Group.ss2 = [] in
  let ttHat = unionL [P.hatVars pure; SS.hatVars ssA; SS.hatVars ssB] in
  let hasTheHat tHat s = List.mem tHat (mkClosureL (S.addrs s)) in
  let sigma1 tHat = List.filter (hasTheHat tHat) ssA in
  let sigma2 tHat = List.filter (hasTheHat tHat) ssB in
  let addr tHat = mkClosureL @@ dropRed (SS.addrs ((sigma1 tHat) @ (sigma2 tHat))) in
  let hasJoinableType tt ttNew =
    match tt,ttNew with
    | [],_ -> true
    | _,[] -> true
    | t1::_,t2::_ ->
       let (u1,u2) = (List.hd (T.getHeadTerm t1), List.hd (T.getHeadTerm t2)) in
       let cond1 =
         let str1 = T.getStructName u1 in
         let str2 = T.getStructName u2 in
         str1 = [] || str2 = [] || str1 = str2
       in
       let cond2 =
         let simp1 = T.getSIMPLEinfo u1 in
         let simp2 = T.getSIMPLEinfo u2 in
         simp1 = [] || simp2 = [] || simp1 = simp2
       in
       cond1 && cond2
  in
  let _G0_body =
    List.map
      (fun tHat -> Group.create (addr tHat) (sigma1 tHat) (sigma2 tHat))
      ttHat
  in
  let _G0_body1 = List.filter (fun g -> not (isEmpGrp g)) _G0_body in
  let _G0 = Groups.create 0 _G0_body1 in
  let _GG = ref [_G0] in
  let _GGtmp = ref [] in
  let _ssA = ref (setminus ssA (List.flatten (List.map (fun tHat -> sigma1 tHat) ttHat))) in
  let _ssB = ref (setminus ssB (List.flatten (List.map (fun tHat -> sigma2 tHat) ttHat))) in
  let _gg = ref [] in
  let checkCond b = if b then () else raise (Error "") in

  (* First part begins *)
  while !_ssA <> [] do
    let s1 = List.hd !_ssA in
    _ssA := List.tl !_ssA;
    let ttAddr = mkClosureL (S.addrs s1) in
    _GGtmp := [];
    for i = 0 to List.length !_GG - 1 do
      let (_G,_GG1) = List_tailrec.takeNth !_GG i in
      let _G' = Groups.push g_emp _G in
      for j = 0 to Groups.length _G' - 1 do
        try 
          let (gj,_Gj) = List_tailrec.takeNth _G'.Groups.body j in
          checkCond @@ (List.filter T.isHCDTVar ttAddr = [] || gj.Group.blktm = []);
          checkCond @@ disjoint ttAddr (List.flatten (List.map (fun g->g.Group.blktm) _Gj));
          checkCond @@ hasJoinableType gj.Group.blktm ttAddr;
          let gj' = Group.create (union ttAddr gj.Group.blktm) (s1 :: gj.Group.ss1) gj.Group.ss2 in
          let gg2 = List_tailrec.replaceNth _G'.Groups.body j gj' in
          let gg3 = List.filter (fun g -> not (isEmpGrp g)) gg2 in
          let _G1' = Groups.create _G'.Groups.id gg3 in
          _GGtmp := _G1' :: !_GGtmp
        with
          Error _ -> ()
      done;
    done;
    _GG := List.rev !_GGtmp;
  done;

  (* Second part begins *)
  while !_ssB <> [] do
    let s2 = List.hd !_ssB in
    _ssB := List.tl !_ssB;
    let ttAddr = mkClosureL (S.addrs s2) in
    _GGtmp := [];
    for i = 0 to List.length !_GG - 1 do
      let (_G,_GG1) = List_tailrec.takeNth !_GG i in
      let _G' = Groups.push g_emp _G in
      for j = 0 to Groups.length _G' - 1 do
        try
          let (gj,_Gj) = List_tailrec.takeNth _G'.Groups.body j in
          checkCond @@ (List.filter T.isHCDTVar ttAddr = [] || gj.Group.blktm = []);
          checkCond @@ List.for_all T.isNotLocalHat gj.Group.blktm;
          checkCond @@ disjoint ttAddr (List.flatten (List.map (fun g->g.Group.blktm) _Gj));
          checkCond @@ hasJoinableType gj.Group.blktm ttAddr;
          let gj' = Group.create (union ttAddr gj.Group.blktm) gj.Group.ss1 (s2 :: gj.Group.ss2) in
          let gg2 = List_tailrec.replaceNth _G'.Groups.body j gj' in
          let gg3 = List.filter (fun g -> not (isEmpGrp g)) gg2 in
          let _G1' = Groups.create _G'.Groups.id gg3 in
          _GGtmp := _G1' :: !_GGtmp
        with
          Error _ -> ()
      done;
    done;
    _GG := List.rev !_GGtmp;
  done;

  Ftools.pf_s tagDebug prerr_endline "Grouping Result";
  Ftools.pf_s tagDebug GG.refreshId !_GG;
  Ftools.pf_s tagDebug GG.println !_GG;
  Ftools.pf_s tagDebug prerr_newline ();
  
  !_GG
;;  

(*-----------------------*)
(* biabduction core      *)
(* (Brotherston's method *)
(*-----------------------*)
(* Brotherston's beta *)
(* "beta p ss1 ss2" returns a pure-formula *)
(* that is equivalent to the biabduction-problem (p,ss1,ss2) has a solution  *)
let beta p ss1 ss2 : P.t list =
  let (ssPto1,ssArr1,ssStr1,ssInd1) = SS.split ss1 in
  let (ssPto2,_,ssStr2,ssInd2) = SS.split ss2 in
  let ttPtoAddr2 = List.flatten @@ List.map S.addrs ssPto2 in
  let segArr1 = List.flatten @@ List.map S.getArraySeg ssArr1 in
  let segStr1 = List.flatten @@ List.map S.getStringSeg ssStr1 in
  let segStr2 = List.flatten @@ List.map S.getStringSeg ssStr2 in
  
  (* condPto: t1->u1 |- t2->u2 satisfies "t1 = t2 implies u1 = u2" *)
  let mkCondPtoOne pto1 pto2 =
    let t1 = List.hd (S.addrs pto1) in
    let t2 = List.hd (S.addrs pto2) in
    let cc1 = S.getPtoContent pto1 in
    let cc2 = S.getPtoContent pto2 in
    let pairs = S.mkContentPairs cc1 cc2 in 
    let cond2 =
      match pairs with
      | [] -> P.True
      | (u1,u2)::[] -> u1 =.= u2
      | _ -> P.And (List.map (fun (u1,u2) -> (u1 =.= u2)) pairs)
    in
    (t1 <.> t2) |.| cond2
  in
  let condPto = 
    let _res = ref [] in
    for i = 0 to List.length ssPto1 - 1 do
      for j = 0 to List.length ssPto2 - 1 do
        let pto1 = List.nth ssPto1 i in
        let pto2 = List.nth ssPto2 j in
        _res := (mkCondPtoOne pto1 pto2) :: !_res 
      done;
    done;
    !_res
  in
  
  (* condPtoArr: Arr(a,b) |- t->_ cannot match "t out [a,b]" *)
  (* condPtoStr: Str(a,b) |- t->_ cannot match "t out [a,b]" *)  
  let mkCondPtoSegOne seg t = List.map (fun (a,b) -> (_Out t a b)) seg in
  let mkCondPtoSeg seg = List.flatten @@ List.map (mkCondPtoSegOne seg) ttPtoAddr2 in
  let condPtoArr = mkCondPtoSeg segArr1 in
  let condPtoStr = mkCondPtoSeg segStr1 in
  
  (* gamma1: ss1 has a model *)
  (* gamma2: ss2 has a model *)  
  let gamma1 = Satcheck.gamma ss1 in
  let gamma2 = Satcheck.gamma ss2 in
  
  (* condPtoStr: t->[0] |- Str(c',d') cannot match "t out [c',d']" *)
  let mkCondNullCharStrOne pto seg =
    let t = List.hd (S.addrs pto) in
    let cc = S.getPtoContent pto in
    match cc with
    | (_,zero)::[] -> List.map (fun (a,b) -> (_Out t a b)) seg
    | _ -> []
  in
  let condNullCharStr = 
    let _res = ref [] in
    for i = 0 to List.length ssPto1 - 1 do
      let pto = List.nth ssPto1 i in
      _res := (mkCondNullCharStrOne pto segStr2) @ !_res
    done;
    !_res
  in

  (* condArrStr: Arr(a,b) |- Str(c',d') cannot match "[a,b] disj [c',d']" *)
  let condArrStr =
    let _res = ref [] in
    for i = 0 to List.length segArr1 - 1 do
      for j = 0 to List.length segStr2 - 1 do
        let (a,b) = List.nth segArr1 i in
        let (c',d') = List.nth segStr2 j in
        _res := (_Disj a b c' d') :: !_res
      done;
    done;
    !_res
  in
  
  [p] @ gamma1 @ gamma2 @ condPtoArr @ condPtoStr @ condPto @ condNullCharStr @ condArrStr
;;

(* rho p ss1 ss2 *)
(* Handling hat variables *)
(* ss1 = Arr(a@hat,a@hat+10) *)
(* ss2 = a@hat+3->() * Arr(b@hat,b@hat+10) *)
(* It makes l0, l1 (lower bound of a@hat- and b@hat-blocks) *)
(* Then rho is *)
(* 0 = l0 < a@hat < a@hat+1 < a@hat+10 < l1 < b@hat < b@hat+10 *)
let rho p ss1 ss2 =
  let ss = ss1 @ ss2 in
  let fvars = union (P.fv p) (SS.fv ss) in
  let fvars_t = union (P.fv_t p) (SS.fv_t ss) in
  let hVars = List.filter T.isHatVar' fvars_t in
  match hVars with
  | [] -> []
  | _ ->
     let _pp = ref [] in
     let ttAddr = union (SS.fv_t ss) (SS.addrs ss) in
     let mkHvarGroup hVar = List.filter (fun t -> List.mem hVar (T.fv_t t)) ttAddr in
     let blkGroups = List.map mkHvarGroup hVars in (* block-groups [ [a@hat;a@hat+3;a@hat+10]; [b@hat;b@hat+10] ] *)
     let blkNumber = List.length blkGroups in
     let ttLowerBounds = List.map (fun v -> T.Var (v,[])) (genFreshVarL "#lb" fvars blkNumber) in
     let lb_0 = List.nth ttLowerBounds 0 in
     (* Lower-bounds' ordering condition *)
     _pp := [lb_0 =.= zero];
     for i = 0 to blkNumber - 2 do
       let lb_i = List.nth ttLowerBounds i in
       let lb_i1 = List.nth ttLowerBounds (i+1) in
       _pp := (lb_i <.< lb_i1) :: !_pp;
     done;
     (* Block-Group range condition except the last group *)
     for i = 0 to blkNumber - 2 do
       let blkGroup_i = List.nth blkGroups i in
       let lb_i = List.nth ttLowerBounds i in
       let lb_i1 = List.nth ttLowerBounds (i+1) in
       for j = 0 to List.length blkGroup_i - 1 do
         let t = List.nth blkGroup_i j in
         _pp := (t <.< lb_i1) :: (lb_i <.< t) :: !_pp
       done;
     done;
     (* Block-Group range condition of the last group *)
     let last = blkNumber - 1 in
     let blkGroup_last = List.nth blkGroups last in
     let lb_last = List.nth ttLowerBounds last in
     for j = 0 to List.length blkGroup_last - 1 do
       let t = List.nth blkGroup_last j in
       _pp := (lb_last <.< t) :: !_pp
     done;
     List.rev !_pp
;;

(* getModelBeta p ss1 ss2 *)
(* This finds a model of the above beta *)
(* It returns Some [("x",1);("y",2)] or None *)
(* The output is the extracted model of a biabduction solution of (p,ss1,ss2) *)
let getModelBeta p ss1 ss2 =
  let vv_p = P.fv p in
  let vv_ss = SS.fv (ss1 @ ss2) in
  let ppVarcond = List.map (fun v -> zero <.= var v []) (vv_p @ vv_ss) in
  let ppBeta = beta p ss1 ss2 in
  let ppRho = rho p ss1 ss2 in
  let eeBeta = List.map Sltosmt.mkExp_p (ppVarcond @ ppBeta @ ppRho) in
(*
  Exp.println eBeta;
 *)
  match Smttoz3.checkSatExpL ~modelflag:true ~ucflag:false eeBeta with
  | SatResult.Model pmodel -> Some pmodel
  | _ -> None

(* mkSolutionPure pmodel ss1 ss2 *)
(* This produces the pure condition for the biabduction solution of (p,ss1,ss2) specified by 'pmodel' *)
let mkSolutionPure pmodel ss1 ss2 : P.t list =
  (* show_pmodel pmodel; *)
  let mkPoints ss =
    let (ssPto,ssArr,ssStr,ssInd) = SS.split ss in
    let ttPtoAddr = List.flatten @@ List.map S.addrs ssPto in
    let segArr = List.flatten @@ List.map S.getArraySeg ssArr in
    let segStr = List.flatten @@ List.map S.getStringSeg ssStr in
    let ttArrPoints = List.flatten @@ List.map (fun (tL,tR) -> [tL;tR;tR +.+ one]) segArr in
    let ttStrPoints = List.flatten @@ List.map (fun (tL,tR) -> [tL;tR;tR +.+ one]) segStr in    
    ttPtoAddr @ ttArrPoints @ ttStrPoints
  in
  let ttPoints = dropRed @@ mkPoints (ss1 @ ss2) in
  let pts_values = List.map (fun t -> (t, SHterm.evalUnderPmodel pmodel t)) ttPoints in
  let pts_values_sorted =
    let compare_pv pv1 pv2 = compare (snd pv1) (snd pv2) in
    List.sort compare_pv pts_values
  in
  let rec mkPure pp pvs =
    match pvs with
    | [] -> List.rev pp
    | _::[] -> List.rev pp
    | (t1,v1)::(t2,v2)::pvs1 ->
       let hVar = union (T.hatVars t1) (T.hatVars t2) in
       begin
         match List.length hVar < 2, v1 = v2 with
         | false,_ -> mkPure pp ((t2,v2)::pvs1)
         | _,true -> mkPure ((t1 =.= t2)::pp) ((t2,v2)::pvs1)
         | _,false -> mkPure ((t1 <.< t2)::pp) ((t2,v2)::pvs1)
       end
  in
  let pp1 = mkPure [] pts_values_sorted in  
  pp1
;;

(* ptocover *)
(* This returns the missing part 't->gg' if it is not covered by 'seg' *)
(* It is Brotherston's ptocov *)
let mkPtoCover pmodel t gg seg =
  let eval t = SHterm.evalUnderPmodel pmodel t in
  let rec aux seg0 = 
    match seg0 with
    | [] -> [S.Pto(t,gg)]
    | (tL,tR)::_ when (eval tL) <= (eval t) && (eval t) <= (eval tR) -> []
    | _ :: seg1 -> aux seg1
  in
  aux seg
;;       

(* blkcover blk tL tR seg *)
(* blk is "arr" or "str" *)
(* This returns the missing (part of) block between tL and tR (Arr if blk="arr", Str if blk="str") *)
(* if it is not covered by 'seg' *)
let mkBlkCover pmodel blk tL tR seg = 
  let eval t = SHterm.evalUnderPmodel pmodel t in
  let blkflag = if blk = "arr" then true else if blk = "str" then false else failwith "blkcover" in
  let rec aux tL0 tR0 seg0 = 
    match blkflag,seg0 with
    | _,_ when (eval tL0) > (eval tR0) -> []
    | true, []          -> [S.Arr(tL0,tR0)]
    | false, []         -> [S.Str(tL0,tR0)]
    | _,(tL1,tR1)::seg1
         when (eval tL) <= (eval tR1) && (eval tL1) <= (eval tR) (* i.e. [tL,tR] comm [tL1,tR1] *)
      -> let ans1 = aux tL0 (tL1 -.- one) seg1 in
         let ans2 = aux (tR1 +.+ one) tR0 seg1 in
         ans1 @ ans2
    | _,_::seg1 -> aux tL0 tR0 seg1
  in
  aux tL tR seg
;;       

let mkCover pmodel s ss =
  let seg = SS.mkSegment ss in
  match s with
  | S.Pto(t,gg) -> mkPtoCover pmodel t gg seg
  | S.Arr(tL,tR) -> mkBlkCover pmodel "arr" tL tR seg
  | S.Str(tL,tR) -> mkBlkCover pmodel "str" tL tR seg
  | S.Ind(p,tt) -> failwith "mkCover: inductive predicate"
;;


(* The core part of biabduction *)
(* Note that this procedure returns only one solution *)
(* If you need multiple solutions, call biabd_core repeatedly changing pure_ex *)
let biabd_core (bq : BAquery.t) : BAanswer.t list =
  let (gid,pp_ex,pure,ss1,ss2) = bq in
  let p = P.And (pure :: pp_ex) in
  match getModelBeta p ss1 ss2 with
  | None ->
     raise Exit
  | Some pmodelBN ->
     let pmodel = List.map (fun (v,bn)->(v,Bignum.to_int bn)) pmodelBN in
     let ppP = mkSolutionPure pmodel ss1 ss2 in
     let ppP' = List.filter (fun p -> not(isValid_pb p)) ppP in
     let ssX = List.flatten @@ List.map (fun s -> mkCover pmodel s ss1) ss2 in
     let ssY = List.flatten @@ List.map (fun s -> mkCover pmodel s ss2) ss1 in
     let biAns = BAanswer.create gid (pp_ex @ ppP') ssX ssY in
     [biAns]
;;


(* CHECK!!!!!!!!!!!! This procedure can be included in biabd_core *)
(* checking solution *)
(* a produced solution should satisfy the following condition *)
(* ss2 <> [] -> forall s in ss1.(cells(s) not sub seg(Y) *)
let checkSolution bq _Y =
  let (pp_ex,p,ss1,ss2) = bq in
  if ss2 = []
  then true
  else
    let segY = SS.mkSegment _Y in
    let mkCondMemOfSegY t = P.And (List.map (fun (u1,u2) -> P.Atom(P.Out,[t;u1;u2])) segY) in
    let expCondMemOfSegY t = mkExp_p (mkCondMemOfSegY t) in
    try
      for i = 0 to List.length ss1 - 1 do
        match List.nth ss1 i with
        | S.Pto(t,_) ->
           let exp = expCondMemOfSegY t in
           begin
             match Smttoz3.checkSatExpBool exp with
             | true -> ()
             | false -> raise Exit
           end
        | S.Arr(t1,t2) | S.Str(t1,t2) ->
           let exp1 = expCondMemOfSegY t1 in
           let exp2 = expCondMemOfSegY t2 in
           let exp = bigOr' [exp1;exp2] in
           begin
             match Smttoz3.checkSatExpBool exp with
             | true -> ()
             | false -> raise Exit
           end
        | S.Ind(_,_) -> failwith "checkSolution"
      done;
      true
    with
      Exit -> false
;;


let biabd_group pure g =
  (* making group-branch *)
  let mkBranch ttMin ttMax tt =
    let _conj = ref [] in
    let _disj = ref [] in
    for i = 0 to List.length ttMin - 1 do
      let tMin = List.nth ttMin i in
      for j = 0 to List.length ttMax - 1 do
        let tMax = List.nth ttMax j in
        _conj := [P.Atom(P.Le,[tMin;tMax])];
        for k = 0 to List.length tt - 1 do
          let t = List.nth tt k in
          if t = tMin || t = tMax then ()
          else 
            _conj := (P.Atom (P.In,[t;tMin;tMax])) :: !_conj;
        done;
        if !_conj = [] then ()       
        else _disj := (P.And !_conj) :: !_disj
      done;
    done;
    P.Or !_disj
  in
  let tt = g.Group.blktm in
  let ttMin =
    match T.hcdtVarsL tt with
    | [] -> tt
    | t::_ -> [t]
  in
  let _p = ref P.True in
  _p := mkBranch ttMin tt tt;
  if !simplFlag
  then
    begin
      Ftools.pf_s tagDebug print_endline "BEFORE SIMPLIFICATION";
      Ftools.pf_s tagDebug P.println !_p;
      _p := simplifyPure !_p;
      Ftools.pf_s tagDebug print_endline "AFTER SIMPLIFICATION";
      Ftools.pf_s tagDebug P.println !_p;
      _p := simplifyPureAtom !_p;
      Ftools.pf_s tagDebug print_endline "AFTER SIMPLIFICATION_ATOM";
      Ftools.pf_s tagDebug P.println !_p
    end
  else ();

  (* Biabduction core *)
  let gid = string_of_int g.Group.gid in
  let ssA = g.Group.ss1 in
  let ssB = g.Group.ss2 in
  let bq = (gid,[!_p],pure,ssA,ssB) in
  let ba = List.hd (biabd_core bq) in (* Note: biabd_core returns a singleton (or raise Exit) *)
  ba
;;

;;
(*-----------------------*)
(* biabduction (whole)   *)
(*-----------------------*)
let biabduction_with_grouping pp_ex pure ss1 ss2 =
  let bq0 = ("",pp_ex,pure,ss1,ss2) in
  let pGamma = P.And (pure :: pp_ex @ (Satcheck.gamma ss1)) in
  if isUnsatPure pGamma
  then
    begin
      Ftools.pf_s tagDebug print_endline "biabduction: the LHS is unsat";
      []
    end
  else
    let _baAnswerL = ref [] in
    let print_baAnswerL () = List.iter BAanswer.println !_baAnswerL in
    let pure0 = P.And (pure :: pp_ex) in
    (* sanitary checking *)
    (* P.checkSan pure0; *)
    SS.checkSan ss1;
    SS.checkSan ss2;
    (* grouping  *)
    let _GG = grouping pure0 ss1 ss2 in
    let _gid = ref "" in
    for j = 0 to List.length _GG - 1 do
    try
      let _Gj = List.nth _GG j in
      let _baL = ref [] in
      for k = 0 to List.length _Gj.Groups.body - 1 do
        let gjk = List.nth _Gj.Groups.body k in
        _gid := "G_" ^ (string_of_int _Gj.Groups.id) ^ "_" ^ (string_of_int k);
        let ba = biabd_group pure0 gjk in (* Note: biabd_group answers a solution or raise Exit *)
        Ftools.pf_s tagDebug prerr_endline ("Biabd_group. Produced solution for " ^ !_gid);
        Ftools.pf_s tagDebug prerr_endline (BAanswer.to_string ba);
        Ftools.pf_s tagDebug prerr_newline ();
        _baL := ba :: !_baL
      done;
      (* producing combined solution of this branch *)
      let gidCombined = "G_" ^ (string_of_int _Gj.Groups.id) in
      let _baCombined = ref (BAanswer.combine !_baL) in
      Ftools.pf_s tagDebug prerr_endline ("Biabd_group: produced solution for " ^ gidCombined);
      Ftools.pf_s tagDebug prerr_endline (BAanswer.to_string !_baCombined);
      (* BEGIN: Solution refinement*)
      if !simplFlag
      then
        begin
          let ssA = List.fold_right (fun g -> fun ss -> g.Group.ss1 @ ss) _Gj.Groups.body [] in
          let ssB = List.fold_right (fun g -> fun ss -> g.Group.ss2 @ ss) _Gj.Groups.body [] in
          let bq = ("",[],pure0,ssA,ssB) in
          _baCombined := BAanswer.refine bq !_baCombined;          
          Ftools.pf_s tagDebug prerr_endline ("Refined Solution");
          Ftools.pf_s tagDebug prerr_endline (BAanswer.to_string !_baCombined)
        end
      else ();
      (* END: Solution refinement*)
      _baAnswerL := !_baCombined :: !_baAnswerL
    with
      Exit ->
      (
        Ftools.pf_s tagDebug prerr_endline ("Biabd_group: failed in finding a solution for " ^ !_gid);
        ()
      )
  done;
  _baAnswerL := List.rev !_baAnswerL;

  Ftools.pf_s tagDebug prerr_endline ("Biabd_group: combined solutions");
  Ftools.pf_s tagDebug print_baAnswerL ();
  Ftools.pf_s tagDebug prerr_newline ();
    
  (* BEGIN: Dropping duplicated solutions *)
  Ftools.pf_s tagTime getTime1 ();  
  (*
  let _cur = ref !_baAnswerL in
  let _prev = ref [] in
  print_endline (string_of_int (List.length !_cur));
  while !_cur <> !_prev do
    _prev := !_cur;
    try
      for i = 0 to List.length !_cur - 1 do
        let (ba1,baL) = List_tailrec.takeNth !_cur i in
        for j = 0 to List.length baL - 1 do
          let ba2 = List.nth baL j in
          match BAanswer.checkQuasiEquality bq0 ba1 ba2 with
          | true -> _cur := baL; raise Skip
          | false -> ()
        done;
      done;
    with
      Skip -> ()
  done;
   *)
  let len = List.length !_baAnswerL in
  let record = ref [true] in
  for i = 0 to len - 1 do
    let baI = List.nth !_baAnswerL i in
    let (ssXi,ssYi) = (baI.BAanswer.ssX,baI.BAanswer.ssY) in
    for j = i+1 to len - 1 do
      let baJ = List.nth !_baAnswerL j in
      let (ssXj,ssYj) = (baJ.BAanswer.ssX,baJ.BAanswer.ssY) in
      if ssXi = ssXj && ssYi = ssYj && BAanswer.checkQuasiEquality bq0 baI baJ
      then record := false :: !record (* false: "it should be eliminated" *)
      else record := true :: !record (* true: "it should not be eliminated" *)
    done;
  done;
  _baAnswerL := List.map fst (List.filter (fun (_,b) -> b) (zipLst !_baAnswerL (List.rev !record)));
  Ftools.pf_s tagTime getTime2 ();
  Ftools.pf_s tagTime showTimeDiff "Kuma";
  (* END: Dropping duplicated solutions *)
  Ftools.pf_s tagDebug prerr_endline ("Biabd_group: dropping duplicated solutions");
  Ftools.pf_s tagDebug print_baAnswerL ();
  Ftools.pf_s tagDebug prerr_newline ();
  
  (* BEGIN: Adding extra pure *)
  let _cur = ref [] in
  Ftools.pf_s tagTime getTime1 ();
  (*
  for i = 0 to List.length !_baAnswerL - 1 do
    let ba = List.nth !_baAnswerL i in
    let pp = extractPureSS (ss1 @ ba.BAanswer.ssX) in
    let pp0 = pp @ ba.BAanswer.pp in
    let pp1 = if !simplFlag then EntlcheckA.simplifyPureL pp0 else pp0 in
    ba.BAanswer.pp <- pp1;
    _cur := ba :: !_cur;
  done;
  *)
  for i = 0 to List.length !_baAnswerL - 1 do
    let ba = List.nth !_baAnswerL i in
    let pp = extractPureSS (ss1 @ ba.BAanswer.ssX) in
    let pp0 = unionL [pp; ba.BAanswer.pp] in
    (* let pp1 = if !simplFlag then EntlcheckA.simplifyPureL pp0 else pp0 in *)
    ba.BAanswer.pp <- pp0;
    _cur := ba :: !_cur;
  done;    
  Ftools.pf_s tagTime getTime2 ();
  Ftools.pf_s tagTime showTimeDiff "Kame";
  _baAnswerL := List.rev !_cur;
  (* END: Adding extra pure *)
  
  Ftools.pf_s tagDebug prerr_endline ("Biabd_group: adding extra pure");
  Ftools.pf_s tagDebug print_baAnswerL ();
  Ftools.pf_s tagDebug prerr_newline ();

  (* BEGIN: Adding the "otherwise" case *)
  let pp = List.map (fun ba -> P.And ba.BAanswer.pp) !_baAnswerL in
  let p = P.Or pp in
  let p1 = if !simplFlag then simplifyPureAtom (P.dual p) else P.dual p in
  begin
    match !_baAnswerL, Smttoz3.checkSatExpBool (mkExp_p p1) with
    | [],_ -> ()
    | _,true ->
       let ba_otherwise = BAanswer.create "OW" [p1] ss2 ss1 in
       _baAnswerL := !_baAnswerL @ [ba_otherwise]            
    | _,false -> ()
  end;
  (* END: Adding the "otherwise" case *)
  
  (* Adding contents condition in the pure-part *)
  List.iter (BAanswer.update_ptocontents bq0) !_baAnswerL;
  !_baAnswerL
;;

let biabductionFW biabd_proc pp_ex pure ss1 ss2 =
  let baAnswers = biabd_proc pp_ex pure ss1 ss2 in
  let baOutput = baSatcheckL pp_ex pure ss1 ss2 baAnswers in
  baOutput
;;  

(*
let biabduction_with_grouping = biabductionFW biabduction_with_grouping0
;;
 *)

(* This is efficient but returns only one solution *)
let biabduction_without_grouping pp_ex pure ss1 ss2 =
  let pGamma = P.And (pure :: pp_ex @ (Satcheck.gamma ss1)) in
  if isUnsatPure pGamma
  then
    begin
      Ftools.pf_s tagDebug prerr_endline "biabduction: the LHS is unsat";
      []
    end
  else 
  let _baAnswerL = ref [] in

  (* sanitary checking *)
  (* P.checkSan (P.And pp_ex); *)
  (* P.checkSan pure; *)
  SS.checkSan ss1;
  SS.checkSan ss2;

  let pure1 = simplifyPureAtom pure in
  let bq = ("",pp_ex,pure1,ss1,ss2) in
  begin
    try
      let baL = biabd_core bq in
      let _ba = ref (List.hd baL) in
      Ftools.pf_s tagDebug prerr_endline ("\nBiabd_without_grouping0: Produced Solution");
      Ftools.pf_s tagDebug prerr_endline (BAanswer.to_string !_ba);

      (* BEGIN: Solution refinement*)
      (* TODO!!!!!!!!!! more efficient refinement algorithm!!!! *)
      if !simplFlag
      then
        begin
          _ba := BAanswer.refine bq !_ba;
          Ftools.pf_s tagDebug prerr_endline ("\nBiabd_without_grouping0: Refined Solution");
          Ftools.pf_s tagDebug prerr_endline (BAanswer.to_string !_ba);
        end
      else ();
      (* END: Solution refinement*)

      _baAnswerL := [!_ba];
    with
      Exit -> ()
  end;
  
  (* BEGIN: Adding the "otherwise" case *)
  let pp = List.map (fun ba -> P.And ba.BAanswer.pp) !_baAnswerL in
  let p = P.Or pp in
  let p1 = simplifyPureAtom (P.dual p) in
  begin
    match !_baAnswerL, Smttoz3.checkSatExpBool (mkExp_p p1) with
    | [],_ -> ()
    | _,true ->
       let ba_otherwise = BAanswer.create "OW" [p1] ss2 ss1 in
       _baAnswerL := !_baAnswerL @ [ba_otherwise]
    | _,false -> ()
  end;
  (* END: Adding the "otherwise" case *)

  (* Adding contents condition in the pure-part *)
  List.iter (BAanswer.update_ptocontents bq) !_baAnswerL;

  !_baAnswerL
;;

(*
let biabduction_without_grouping = biabductionFW biabduction_without_grouping0
;;
 *)

(* Avoiding zero_div exception *)
let avoid_zero_div_exception pp_ex pure ss1 ss2 =
  let ttDenoms =
    let pp = pure :: pp_ex in
    let denoms = SS.denominators (ss1 @ ss2) in
    unionL (denoms :: (List.map P.denominators pp))
  in
  let ppZeroLtDenoms = List.map (fun t -> zero <.< t) ttDenoms in
  let pp_ex1 = ppZeroLtDenoms @ pp_ex in
  (pp_ex1,pure,ss1,ss2)
;;

(* biabductionArray
it returns ba_output = ([baAnswers],pp),
where 
baAnswers are sat solutions
pp are pure-conditions of unsat solutions
*)
let biabductionArray pp_ex pure ss1 ss2 : BAoutput.t =
  let p1 = P.And (pure::pp_ex) in
  let _ss1 = ref ss1 in
  let _ss2 = ref ss2 in
  Ftools.pf_s tagDebug print_endline "biabduction for Arrays";
  Ftools.pf_s tagDebug print_endline ("P: " ^ P.to_string p1);
  Ftools.pf_s tagDebug print_endline ("A: " ^ SS.to_string !_ss1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ SS.to_string !_ss2);
  let len1 = List.length !_ss1 in
  let len2 = List.length !_ss2 in
  let maxsize = 100 in  
  match !grpFlag, (len1+len2 < maxsize) with
  | true,true ->
     (* new version (several solutions) *)
     Ftools.pf_s tagDebug print_endline "biabduction: GROUPING-MODE";     
     let baAnswerL = biabduction_with_grouping pp_ex pure !_ss1 !_ss2 in
     let baOutput = baSatcheckL pp_ex pure ss1 ss2 baAnswerL in
     baOutput
  | true,_ ->
     (* almost old version *)
     let mes = " (because of the size of input > " ^ (string_of_int maxsize) ^ ")" in     
     Ftools.pf_s tagDebug print_endline ("biabduction: NON-GROUPING-MODE" ^ mes);
     let baAnswerL = biabduction_without_grouping pp_ex pure !_ss1 !_ss2 in
     let baOutput = baSatcheckL pp_ex pure ss1 ss2 baAnswerL in
     baOutput
  | false,_ ->
     Ftools.pf_s tagDebug print_endline "biabduction: NON-GROUPING-MODE (grouping flag is OFF)";
     let baAnswerL = biabduction_without_grouping pp_ex pure !_ss1 !_ss2 in
     let baOutput = baSatcheckL pp_ex pure ss1 ss2 baAnswerL in
     baOutput
;;  

(* NOT YET DUMMY *)
let biabductionList pp_ex pure ss1 ss2 : BAoutput.t =
  Ftools.pf_s tagDebug print_endline "biabduction for Lists";
  match ss1,ss2 with
  | [],[] ->
     let baAnswer = BAanswer.create "" [] [] [] in
     ([baAnswer],[])
  | [],_ ->
     let baAnswer = BAanswer.create "" [] [] ss2 in
     ([baAnswer],[])
  | _,[] ->
     let baAnswer = BAanswer.create "" [] ss1 [] in
     ([baAnswer],[])
  | _,_ ->
     let pp = pure::pp_ex in
     let p1 = P.And (pure :: pp_ex) in
     if isUnsatPure p1
     then
       begin
         Ftools.pf_s tagDebug print_endline "biabductionList: the LHS is unsat";
         let baAnswer = BAanswer.create "" [] [] [] in
         ([baAnswer],[])
       end
     else
       begin
         let solutionL = Biabdls.biabduction pp ss1 ss2 in
         let _output = ref [] in
         for i = 0 to List.length solutionL - 1 do
           let ((pp,ssX),(_,ssY)) = List.nth solutionL i in
           let i' = string_of_int i in 
           let ans = BAanswer.create ("Ls" ^ i') pp ssX ssY in
           sayIfDebugLazy (fun _ -> (BAanswer.to_string ans));
           _output := ans :: !_output
         done;
         (List.rev !_output,[])
       end
;;  

let biabduction2_core pp_ex pure ss1 ss2 : BAoutput.t =
  let p1 = P.And (pure::pp_ex) in
  let _ss1 = ref ss1 in
  let _ss2 = ref ss2 in
  (* Indirect-folding *)
  Ftools.pf_s tagDebug print_endline "biabduction: Folding Indirects";
  _ss1 := SS.fold_indirect !_ss1;
  _ss2 := SS.fold_indirect !_ss2;
  Ftools.pf_s tagDebug print_endline ("P: " ^ P.to_string p1);
  Ftools.pf_s tagDebug print_endline ("A: " ^ SS.to_string !_ss1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ SS.to_string !_ss2);
  Ftools.pf_s tagDebug print_newline ();
  
  (* Avoiding Zero-dividing *)
  Ftools.pf_s tagDebug print_endline "biabduction: Avoid Zero-dividing";  
  let (pp_ex,pure,ss1',ss2') = avoid_zero_div_exception pp_ex pure !_ss1 !_ss2 in
  _ss1 := ss1';
  _ss2 := ss2';
  Ftools.pf_s tagDebug print_endline ("P: " ^ P.to_string p1);
  Ftools.pf_s tagDebug print_endline ("A: " ^ SS.to_string !_ss1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ SS.to_string !_ss2);
  Ftools.pf_s tagDebug print_newline ();
  
  (* Separating Non-Presburger terms *)
  let _vv = ref [] in
  let _eqlist = ref [] in
  let print_eqlist () =
    print_endline @@
      "[" ^ (string_of_list (fun (t,v) -> "(" ^ (T.to_string t) ^ "," ^ v ^ ")") "," !_eqlist) ^ "]"
  in  
  let pp_ex' = List.map (P.extract_nonPb _vv _eqlist) pp_ex in
  let pure' = P.extract_nonPb _vv _eqlist pure in
  _ss1 := SS.extract_nonPb _vv _eqlist !_ss1;
  _ss2 := SS.extract_nonPb _vv _eqlist !_ss2;
  Ftools.pf_s tagDebug print_endline "biabduction: Separation of Non-Presburger terms";
  Ftools.pf_s tagDebug print_eqlist ();
  Ftools.pf_s tagDebug print_endline ("P1: " ^ (P.to_string (P.And pp_ex')));  
  Ftools.pf_s tagDebug print_endline ("P2: " ^ P.to_string pure');
  Ftools.pf_s tagDebug print_endline ("A: " ^ SS.to_string !_ss1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ SS.to_string !_ss2);
  Ftools.pf_s tagDebug print_newline ();
  
  (* Splitting Arrays and Lists *)
  Ftools.pf_s tagDebug print_endline "biabduction: Splitting Array-part and List-part";
  let (ssArr1,ssLs1) = SS.splitArrayList !_ss1 in
  let (ssArr2,ssLs2) = SS.splitArrayList !_ss2 in
  Ftools.pf_s tagDebug print_endline ("ArrL: " ^ (SS.to_string ssArr1));
  Ftools.pf_s tagDebug print_endline ("ArrR: " ^ (SS.to_string ssArr2));
  Ftools.pf_s tagDebug print_endline ("Ls-L: " ^ (SS.to_string ssLs1));
  Ftools.pf_s tagDebug print_endline ("Ls-R: " ^ (SS.to_string ssLs2));    
  Ftools.pf_s tagDebug print_newline ();

  (* Calling biabduction for Arrays and Lists *)
  let (baArrL,ppArr) = biabductionArray pp_ex' pure' ssArr1 ssArr2 in
  let (baLsL,ppLs) = biabductionList pp_ex' pure' ssLs1 ssLs2 in

  (* Combining Answers *)
  let baL = BAanswer.combineL baArrL baLsL in
  let ppEx = ppArr @ ppLs in
  let _baOutput = ref (baL,ppEx) in
  
  (* Returning Non-Presburger terms *)
  Ftools.pf_s tagDebug print_endline "Returning Non-Presburger terms";
  Ftools.pf_s tagDebug print_endline "Before:";
  Ftools.pf_s tagDebug BAoutput.println !_baOutput;
  let sub = List.map (fun (nonPb,v) -> (v,nonPb)) !_eqlist in
  _baOutput := BAoutput.subst sub !_baOutput;
  Ftools.pf_s tagDebug print_endline "After:";
  Ftools.pf_s tagDebug BAoutput.println !_baOutput;
  Ftools.pf_s tagDebug print_newline ();
  
  (* Indirect-unfolding *)
  Ftools.pf_s tagDebug print_endline "biabduction: Unfolding Indirects";
  _baOutput := BAoutput.unfold_indirect !_baOutput;
  Ftools.pf_s tagDebug BAoutput.println !_baOutput;
  Ftools.pf_s tagDebug print_newline ();

  !_baOutput
;;


let biabduction2 pp_ex pure ss1 ss2 : BAoutput.t =
  match ss1,ss2 with
  | [],_ -> (* special case: ss1=Emp *)
     let ans = BAanswer.create "" (pp_ex @ [pure]) ss2 [] in
     ([ans],[])
  | _,[] ->  (* special case: ss2=Emp *)
     let ans = BAanswer.create "" (pp_ex @ [pure]) [] ss1 in
     ([ans],[])
  | _,_ -> (* normal case *)
     biabduction2_core pp_ex pure ss1 ss2
;;



let biabduction pp_ex pure ss1 ss2 : BAanswer.t list =
  let (pp_ex,pure,ss1,ss2) = avoid_zero_div_exception pp_ex pure ss1 ss2 in
  let len1 = List.length ss1 in
  let len2 = List.length ss2 in
  let maxsize = 100 in
  match ss1,ss2, !grpFlag, (len1+len2 < maxsize) with
  | [],_,_,_ ->
     let ans = BAanswer.create "" (pp_ex @ [pure]) ss2 [] in
     [ans]
  | _,[],_,_ ->
     let ans = BAanswer.create "" (pp_ex @ [pure]) [] ss1 in
     [ans]
  | _,_,true,true ->
     Ftools.pf_s tagDebug print_endline "biabduction: GROUPING-MODE";
     biabduction_with_grouping pp_ex pure ss1 ss2
  | _,_,true,_ ->
     let mes = " (because of the size of input > " ^ (string_of_int maxsize) ^ ")" in
     Ftools.pf_s tagDebug print_endline ("biabduction: NON-GROUPING-MODE" ^ mes);
     biabduction_without_grouping pp_ex pure ss1 ss2
  | _,_,false,_ ->
     Ftools.pf_s tagDebug print_endline "biabduction: NON-GROUPING-MODE (grouping flag is OFF)";
     biabduction_without_grouping pp_ex pure ss1 ss2
;;  

