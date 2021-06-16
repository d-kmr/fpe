open Slsyntax
open Tools
module SatResult = Smttoz3.SatcheckResult
;;

exception NoAnswer
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
let sayIfDebugLazy arg = doIfDebug print_endline (arg ())
;;
let ( |= ) pp p = Sltosmt.entailPure pp p
;;
let ( |== ) pp pp1 = pp |= (P.And pp1)
;;
let ( |/= ) pp p = not (Sltosmt.entailPure pp p)
;;
let ( |/== ) pp pp1 = pp |/= (P.And pp1)
;;
let tagDebug = "BIABD_debug"
;;

(* cc1 and cc2 are assumed to be sorted *)
let rec zipcc cc1 cc2 =
  match cc1,cc2 with
  | [],[] -> []
  | (f1,u1)::cc1',(f2,u2)::cc2' when f1 = f2 ->
     (u1,u2) :: (zipcc cc1' cc2')
  | _ -> raise NoAnswer
;;
let isMemPP pp t uu =
  List.exists (fun u -> pp |= (t =.= u)) uu
;;
let rec findCommonPP pp tt uu =
  match tt with
  | [] -> None
  | t::tt1 ->
     if isMemPP pp t uu
     then Some t
     else findCommonPP pp tt1 uu
;;

module Path = struct

  (* 'e' is used *)
  type endpoint =
    | P of (bytes * T.t) list * T.t
    | L of T.t
    
  (* 'q' is used *)
  (* (x,[P([],y)],y) means x->(next:y)  *)
  (* (x,[L(a);L(b);P([],y)],y) means Ls(x,a) * Ls(a,b) * b->(next:y) *)
  type t = T.t * endpoint list * T.t

  let emp t = (t,[],t)

  let dummy = emp (T.Int 0)
            
  let to_string (q:t) =
    let rec aux str ee =
      match ee with
      | [] -> str
      | (P(_,u)) :: ee1 ->
         let u' = T.to_string u in
         aux (str ^ " -> " ^ u') ee1
      | (L u) :: ee1 ->
         let u' = T.to_string u in
         aux (str ^ " --> " ^ u') ee1
    in
    let (t,ee,u) = q in
    let t' = T.to_string t in
    match ee with
    | [] ->
       let u' = T.to_string u in
       t' ^ "-->" ^ u'
    | _ ->
       aux t' ee
      
  let println q = print_endline (to_string q)

  let fromSpatExp s : t =
    match s with
    | S.Pto(t,cc) ->
       let u =
         try List.assoc "next" cc with
           Not_found -> failwith "Biabd_list.SpatExp.fromSpatExp: Pto"
       in
       (t, [P(cc,u)], u)
    | S.Ind (p,t::u::_) when p = "Ls" ->
       (t, [L(u)], u)
    | S.Ind _ -> failwith "Biabd_list.SpatExp.fromSpatExp: Ind"
    | S.Arr _ -> failwith "Biabd_list.SpatExp.fromSpatExp: Arr"
    | S.Str _ -> failwith "Biabd_list.SpatExp.fromSpatExp: Str"

  let toSpat (q:t) : SS.t =
    let (t,ee,u) = q in
    let _t = ref t in
    let _res = ref [] in
    for i = 0 to List.length ee - 1 do
      match List.nth ee i with
      | P(cc,u) ->
         _res := (S.Pto(!_t,cc)) :: !_res;
         _t := u;
      | L u ->
         _res := (S.Ind("Ls",[!_t;u])) :: !_res;
         _t := u;
    done;
    List.rev !_res

  let get_endpoint_e e =
    match e with
    | P(_,u) -> u
    | L u -> u

  let get_endpoint_ee ee = List.map get_endpoint_e ee
    
  let get_endpoint (q:t) =
    let (t,ee,_) = q in
    t :: (get_endpoint_ee ee)

  let toPP pp (q: t) =
    let rec get_next_ep res ee =
      match ee with
      | [] -> res
      | P(_,u)::ee1 -> get_next_ep (u::res) ee1
      | L(_)::ee1 -> get_next_ep res ee1
    in
    let (t,ee,u) = q in
    if ee = [] then pp
    else
      let vv = t :: (List.tl (get_next_ep [] ee)) in
      let _pp = ref pp in
      for i = 0 to List.length vv - 1 do
        for j = i+1 to List.length vv - 1 do
          _pp := ((List.nth vv i) <.> (List.nth vv j)) :: !_pp
        done;
      done;
      !_pp
    
  let head (q:t) = fst3 q

  let tail (q:t) =
    let ee = snd3 q in
    get_endpoint_ee ee
                 
  let append pp q1 q2 =
    (* (true,q) if append is executed *)
    (* (false,dummy) otherwise *)
    let (t1,ee1,u1) = q1 in 
    let (t2,ee2,u2) = q2 in
    match Sltosmt.entailPure pp (u1 =.= t2) with
    | true -> (true,(t1,ee1@ee2,u2))
    | false ->        
       match Sltosmt.entailPure pp (u2 =.= t1) with
       | true -> (true,(t2,ee2@ee1,u1))
       | false -> (false,dummy)

  (* checking a path is a cycle (not rho-form) *)
  let isCycle pp (q:t) =
    let (t,ee,u) = q in
    Sltosmt.entailPure pp (t =.= u) && ee <> []
               
  let rotate (q:t) =
    let (t,ee,_) = q in
    match ee with
    | [] -> q
    | [_] -> q
    | e1::e2::ee3 ->
       let t1 = get_endpoint_e e1 in
       let q' = (t1, e2::ee3@[e1], t1) in
       q'

  (* rotate_cycle x (y->x->y) is (x->y->x) *)
  let rotate_cycle pp t (q : t) = 
    let _q = ref q in
    while (pp |/= (t =.= head !_q)) do
      _q := rotate !_q;
    done;
    !_q
    
end
;;

module Paths = struct

  type t = Path.t list

  let to_string (qq : t) =
    string_of_list (fun x->x) " * " (List.map Path.to_string qq)

  let println qq = print_endline (to_string qq)

  let fromSpat (ss : SS.t) : t =
    match ss with
    | [] -> [Path.dummy]
    | _ -> List.map Path.fromSpatExp ss

  let toSpat (qq : t) : SS.t = List.flatten (List.map Path.toSpat qq) 
                           
  let appendL pp (qq : t) = 
    let n = List.length qq in
    let a = Array.make n (true,Path.dummy) in
    let _execflag = ref false in
    (* initialization *)
    for i = 0 to n - 1 do
      a.(i) <- (true,List.nth qq i)
    done;
    (* execute append *)
    for i = 0 to n - 1 do
      let qi = snd a.(i) in
      try
        for j = i+1 to n - 1 do
          let qj = snd a.(j) in
          let (b,q1) = Path.append pp qi qj in
          if b
          then
            begin
              a.(j) <- (true,q1);
              a.(i) <- (false,Path.dummy);
              _execflag := true;
              raise Exit
            end
          else ()
        done;
      with
        _ -> ()
    done;
    let qq' = List.map snd @@ List.filter (fun (b,_)->b) (Array.to_list a) in
    (!_execflag,qq')
         
  let normalize pp (qq : t) : t =
    let _qq = ref qq in
    let _exit = ref false in
    while (not !_exit) do
      let (b,qq1) = appendL pp !_qq in
      _qq := qq1;
      if b
      then ()
      else _exit := true;
    done;
    !_qq

  let rotate_cycles pp qq1 qq2 =
    (* rotation of qq1 *)
    let _qq1 = ref [] in
    for i = 0 to List.length qq1 - 1 do
      let q = List.nth qq1 i in
      let ttHeads = List.map Path.head qq2 in
      match Path.isCycle pp q with
      | false -> _qq1 := q :: !_qq1
      | true ->
         let ttTails = Path.tail q in
         match intersect ttTails ttHeads with
         | [] -> _qq1 := q :: !_qq1
         | t::_ -> _qq1 := (Path.rotate_cycle pp t q) :: !_qq1
    done;
    _qq1 := List.rev !_qq1;
    (* rotation of qq2 *)    
    let _qq2 = ref [] in    
    for i = 0 to List.length qq2 - 1 do
      let q = List.nth qq2 i in
      let ttHeads = List.map Path.head qq1 in
      match Path.isCycle pp q with
      | false -> _qq2 := q :: !_qq2
      | true ->
         let ttTails = Path.tail q in
         match intersect ttTails ttHeads with
         | [] -> _qq2 := q :: !_qq2
         | t::_ -> _qq2 := (Path.rotate_cycle pp t q) :: !_qq2
    done;
    _qq2 := List.rev !_qq2;    
    (!_qq1,!_qq2)
    
end
;;

module BAsh = struct

  type t = P.t list * Paths.t
         
  let join (a1: t) (a2: t) : t =
    let (pp1,qq1) = a1 in
    let (pp2,qq2) = a2 in
    (pp1@pp2, qq1@qq2)

  let to_string (a: t) =
    let (pp,qq) = a in
    let pp' = P.to_string (P.And pp) in
    let qq' = Paths.to_string qq in
    match pp,qq with
    | [],[] -> "Emp"
    | _,[] -> pp'
    | [],_ -> qq'
    | _,_ -> pp' ^ " & " ^ qq'

  let println a = print_endline (to_string a)
    
  let toSH (a: t) =
    let (pp,qq) = a in
    let p = P.And pp in
    let ss = Paths.toSpat qq in
    (p,ss)

  let toSH' (a: t) =
    let (pp,qq) = a in
    let ss = Paths.toSpat qq in
    (pp,ss)
    
  let satcheck ~modelflag ~ucflag ~bnflag (a: t) =
    let sh = toSH a in
    Satcheck.satcheck_bn modelflag ucflag bnflag sh
    
end
;;

let biabduction_core preciseflag pp q1 aX q2 aY =
  (* if preciseflag = true, it works more precise with many solutions *)
  let rec biabd pp q1 aX q2 aY =
    (*
    let print_debug () =
      let pp' = P.to_string (P.And pp) in
      let q1' = Path.to_string q1 in
      let aX' = BAsh.to_string aX in
      let q2' = Path.to_string q2 in
      let aY' = BAsh.to_string aY in
      print_endline @@ "$ Biabd(" ^ pp'  ^ "," ^ q1' ^ "," ^ aX' ^ "," ^ q2' ^ "," ^ aY' ^ ")"
    in
     *)
    let (t1,ee1,u1) = q1 in
    let (t2,ee2,u2) = q2 in
    let t1_eq_t2 = t1 =.= t2 in
    let _eeA = ref [] in
    let _e = ref [] in
    let _eeB = ref [] in    
    match ee1,ee2 with
    (* EmpLR *)      
    | [],[] ->
       let t1_eq_u1 = (t1 =.= u1) in
       let t1_eq_u1_is_triv = ((Path.toPP pp q1) |= t1_eq_u1) in
       let t2_eq_u2 = (t2 =.= u2) in
       let a = BAsh.join aX (t1_eq_u1 :: pp,[]) in       
       begin
         match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true a, (t1_eq_u1::pp |= t2_eq_u2) with
         | SatResult.Model _,true -> 
            let aX' = if t1_eq_u1_is_triv then aX else BAsh.join aX ([t1_eq_u1],[]) in
            let aY' = aY in
            [(aX',aY')]
         | _,_ -> []
       end      
    (* EmpL *)
    | [],_ ->
       let t1_eq_u1 = (t1 =.= u1) in
       let t1_eq_u1_is_triv = ((Path.toPP pp q1) |= t1_eq_u1) in
       let a = BAsh.join aX (t1_eq_u1 :: pp,[q2]) in
       let aX' = if t1_eq_u1_is_triv then BAsh.join aX ([],[q2]) else BAsh.join aX ([t1_eq_u1],[q2]) in
       let aY' = aY in
       begin
         match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true a with
         | SatResult.Model _ -> [(aX',aY')]
         | _ -> []
       end
    (* EmpR *)       
    | _,[] ->
       let t2_eq_u2 = (t2 =.= u2) in
       let t2_eq_u2_is_triv = ((Path.toPP pp q1) |= t2_eq_u2) in
       let aX' = if t2_eq_u2_is_triv then aX else BAsh.join ([t2_eq_u2],[]) aX in
       let aY' = BAsh.join ([],[q1]) aY in
       [(aX',aY')]
    (* Match-PP *)
    | Path.P(cc1,v1)::ee1', Path.P(cc2,v2)::ee2' when (pp |= t1_eq_t2) -> 
       begin
         try
           let cc1sorted = List.sort order2 cc1 in
           let cc2sorted = List.sort order2 cc2 in
           let tPairs = zipcc cc1sorted cc2sorted in
           let tt1_eq_tt2 = List.map (fun (t1,t2) -> (t1 =.= t2)) tPairs in
           let tt1_eq_tt2_is_triv = ((Path.toPP pp q1) |== tt1_eq_tt2) in
           let pp' = if tt1_eq_tt2_is_triv then pp else (tt1_eq_tt2 @ pp) in
           let q1' = (v1,ee1',u1) in
           let q2' = (v2,ee2',u2) in
           let aX' = if tt1_eq_tt2_is_triv then aX else BAsh.join (tt1_eq_tt2,[]) aX in
           let aY' = aY in
           match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true (BAsh.join (pp',[q1']) aX') with
           | SatResult.Model _ -> biabd pp' q1' aX' q2' aY'
           | _ -> raise NoAnswer
         with
           NoAnswer -> []
       end
   (* Match-PL *)
    | Path.P(cc1,v1)::ee1', Path.L(v2)::ee2' when (pp |= t1_eq_t2) ->
       (* |Ls(t2,v2)| = 0 *)
       let biabd0 =
         begin
           try
             let t2_eq_v2 = (t2 =.= v2) in
             let t2_eq_v2_is_triv = ((Path.toPP pp q1) |= t2_eq_v2) in
             let pp' = if t2_eq_v2_is_triv then pp else (t2_eq_v2 :: pp) in
             let q1' = q1 in
             let q2' = (v2,ee2',u2) in
             let aX' = if t2_eq_v2_is_triv then aX else BAsh.join ([t2_eq_v2],[]) aX in
             let aY' = aY in
             match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true (BAsh.join (pp',[q1']) aX') with
             | SatResult.Model _ -> biabd pp' q1' aX' q2' aY'
             | _ -> raise NoAnswer
           with
             NoAnswer -> []
         end
       in
       (* |Ls(t2,v2)| >= 1 *)       
       let biabd1 =
         begin
           try
             let t2_neq_v2 = (t2 <.> v2) in
             let t2_neq_v2_is_triv = ((Path.toPP pp q1) |= t2_neq_v2) in
             let pp' = if t2_neq_v2_is_triv then pp else (t2_neq_v2 :: pp) in
             let q1' = (v1,ee1',u1) in
             let q2' = (v1,Path.L(v2)::ee2',u2) in
             let aX' = if t2_neq_v2_is_triv then aX else BAsh.join ([t2_neq_v2],[]) aX in
             let aY' = aY in
             match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true (BAsh.join (pp',[q1']) aX') with
             | SatResult.Model _ -> biabd pp' q1' aX' q2' aY'
             | _ -> raise NoAnswer
           with
             NoAnswer -> []
         end
       in
       biabd0 @ biabd1
    (* Match-LP *)
    | Path.L(v1)::ee1', Path.P(cc2,v2)::ee2' when (pp |= t1_eq_t2) ->
       (* only |Ls(t1,v1)| = 0 *)
       begin
         try
           let t1_eq_v1 = (t1 =.= v1) in
           let t1_eq_v1_is_triv = ((Path.toPP pp q1) |= t1_eq_v1) in
           let pp' = if t1_eq_v1_is_triv then pp else (t1_eq_v1 :: pp) in
           let q1' = (v1,ee1',u1) in
           let q2' = q2 in
           let aX' = if t1_eq_v1_is_triv then aX else BAsh.join ([t1_eq_v1],[]) aX in
           let aY' = aY in
           match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true (BAsh.join (pp',[q1']) aX') with
           | SatResult.Model _ -> biabd pp' q1' aX' q2' aY'
           | _ -> raise NoAnswer
         with
           NoAnswer -> []
       end
    (* Match-LL *)
    | Path.L(v1)::ee1', Path.L(v2)::ee2' when (pp |= t1_eq_t2) ->
       (* |Ls(t1,v1)| >= |Ls(t2,v2)| *)
       let biabd1 =
         let pp' = pp in
         let q1' = (v2,Path.L(v1)::ee1',u1) in
         let q2' = (v2,ee2',u2) in
         let aX' = aX in
         let aY' = aY in
         biabd pp' q1' aX' q2' aY'
       in
       (* |Ls(t1,v1)| < |Ls(t2,v2)| *)
       let biabd2 =
         let pp' = pp in
         let q1' = (v1,ee1',u1) in
         let q2' = (v1,Path.L(v2)::ee2',u2) in
         let aX' = aX in
         let aY' = aY in
         biabd pp' q1' aX' q2' aY'
       in
       biabd1 @ biabd2
    (* Match-MidL *)
    | _,_ when
           begin
             _eeA := [];
             _eeB := ee1;
             _e := [];
             try
               for i = 0 to List.length ee1 - 1 do
                 let e = List.hd !_eeB in
                 _eeB := List.tl !_eeB;                 
                 let w = Path.get_endpoint_e e in
                 if (pp |= (t2 =.= w)) then (_e := [e]; raise Exit) else (_eeA := e::!_eeA)
               done;
             with Exit -> ()
           end;
           !_e <> []
      ->
       let ee11 = !_eeA in
       let e1 = List.hd !_e in
       let ee12 = !_eeB in
       let pp' = pp in
       let q1' = (t2,ee12,u1) in
       let q2' = (t2,ee2,u2) in
       let aX' = aX in
       let aY' = BAsh.join ([],[(t1,ee11@[e1],t2)]) aY in
       biabd pp' q1' aX' q2' aY'
    (* Match-MidR *)
    | _,_ when
           begin
             _eeA := [];
             _eeB := ee2;
             _e := [];
             try
               for i = 0 to List.length ee2 - 1 do
                 let e = List.hd !_eeB in
                 _eeB := List.tl !_eeB;                 
                 let w = Path.get_endpoint_e e in
                 if (pp |= (t1 =.= w)) then (_e := [e]; raise Exit) else (_eeA := e::!_eeA)
               done;
             with Exit -> ()
           end;
           !_e <> []
      ->
       let ee21 = !_eeA in
       let e2 = List.hd !_e in
       let ee22 = !_eeB in
       let pp' = pp in
       let q1' = (t1,ee1,u1) in
       let q2' = (t1,ee22,u2) in
       let aX' = BAsh.join ([],[(t2,ee21@[e2],t1)]) aX in
       let aY' = aY in
       biabd pp' q1' aX' q2' aY'
       
    (* UnMatch-precise *)
    | _,_ when preciseflag ->
       (* No-match *)
       let biabd0 =
         let aX' = BAsh.join ([],[q2]) aX in
         let aY' = BAsh.join ([],[q1]) aY in
         [(aX',aY')]
       in
       (* let heads be matched *)
       let biabd1 =
         match (pp |= t1_eq_t2) with
         | false -> []
         | true -> 
            let pp' = t1_eq_t2 :: pp in
            let q1' = q1 in
            let q2' = q2 in
            let aX' = BAsh.join ([t1_eq_t2],[]) aX in
            let aY' = aY in
            biabd pp' q1' aX' q2' aY'
       in
       let _solution = ref (biabd0 @ biabd1) in
       (* let each middle of ee1 match with t2 *)
       _eeA := [];
       _eeB := ee1;
       for i = 0 to List.length ee1 - 1 do
         let e1 = List.hd !_eeB in
         _eeB := List.tl !_eeB;
         let t2_eq_e1 = (t2 =.= Path.get_endpoint_e e1) in
         let pp' = (t2_eq_e1 :: pp) in
         match Sltosmt.isSatPureL pp' with
         | SatResult.Model _ ->
            let ee11 = List.rev !_eeA in
            let ee12 = !_eeB in
            let q1' = (t2,ee12,u1) in
            let q2' = (t2,ee2,u2) in
            let aX' = BAsh.join ([t2_eq_e1],[]) aX in
            let aY' = BAsh.join ([],[(t1,ee11@[e1],t2)]) aY in
            _solution := (biabd pp' q1' aX' q2' aY') @ !_solution;
            _eeA := e1 :: !_eeA;
         | _ -> ()
       done;
       (* let each middle of ee2 match with t1 *)
       _eeA := [];
       _eeB := ee2;
       for i = 0 to List.length ee2 - 1 do
         let e2 = List.hd !_eeB in
         _eeB := List.tl !_eeB;
         let t1_eq_e2 = (t1 =.= Path.get_endpoint_e e2) in
         let pp' = (t1_eq_e2 :: pp) in
         match Sltosmt.isSatPureL pp' with
         | SatResult.Model _ ->
            let ee21 = List.rev !_eeA in
            let ee22 = !_eeB in
            let q1' = (t1,ee1,u1) in
            let q2' = (t1,ee22,u2) in
            let aX' = BAsh.join ([t1_eq_e2],[(t2,ee21@[e2],t1)]) aX in
            let aY' = aY in
            _solution := (biabd pp' q1' aX' q2' aY') @ !_solution;
            _eeA := e2 :: !_eeA;
         | _ -> ()
       done;
       !_solution

    (* UnMatch-imprecise *)
    | _,_ ->
       let aX' = BAsh.join ([],[q2]) aX in
       let aY' = BAsh.join ([],[q1]) aY in
       [(aX',aY')]
  in
  biabd pp q1 aX q2 aY
;;

(* Grouping *)
(* grouping_one *)
(* a->b->c->d->e and [b->c;d->e->f;x->y] returns (a->b->c->d->e->f,x->y,[c->d])*)
let grouping_one pp q qq aX =
  let tt = Path.get_endpoint q in
  let give_index q1 =
    let uu = Path.get_endpoint q1 in
    let _idx = ref (-1) in
    begin
      try
        for i = 0 to List.length tt - 1 do
          let t = List.nth tt i in
          for j = 0 to List.length uu - 1 do
            let u = List.nth uu j in
            if (pp |= (t =.= u)) then (_idx := i; raise Exit) else ()
          done;
        done;
      with
        Exit -> ()
    end;
    !_idx
  in
  let qqI = List.map (fun q -> (give_index q,q)) qq in
  let (qqI1,qqI2) = List.partition (fun (i,_) -> i <> -1) qqI in
  let qq1 = List.map snd (List.sort order2 qqI1) in
  let qq2 = List.map snd qqI2 in
  match qq1 with
  | [] -> None (* no element related to q in qq *)
  | (v,ee,w)::qq1' ->
     let start = v in
     let _last = ref w in
     let _ee = ref (List.rev ee) in
     let _aX = ref aX in
     for i = 0 to List.length qq1' - 1 do
       let (v1,ee1,w1) = List.nth qq1' i in
       _ee := (List.rev ee1) @ [Path.L(v1)] @ !_ee;
       _aX := BAsh.join !_aX ([],[(!_last,[Path.L(v1)],v1)]);
       _last := w1;
     done;
     match BAsh.satcheck ~modelflag:false ~ucflag:false ~bnflag:true (BAsh.join (pp,[]) !_aX) with
     | SatResult.Model _ -> 
        let qA = (start,List.rev !_ee,!_last) in
        Some (qA,qq2,!_aX)
     | _ -> raise NoAnswer
;;

let grouping_by_pingpong pp q1 qq1 aX qq2 aY =
  let _q1 = ref q1 in
  let _q2 = ref Path.dummy in
  let _qq1 = ref qq1 in
  let _qq2 = ref qq2 in
  let _aX = ref aX in
  let _aY = ref aY in
  let _exec1 = ref true in
  let _exec2 = ref true in
  while !_exec1 || !_exec2 do
    _exec1 := true; _exec2 := true;
    begin (* ping *)
      match grouping_one pp !_q1 !_qq2 !_aY with
      | None -> _exec1 := false
      | Some(q2',qq2',aY') -> _q2 := q2'; _qq2 := qq2'; _aY := aY'
    end;
    begin (* pong *)
      match grouping_one pp !_q2 !_qq1 !_aX with
      | None -> _exec2 := false
      | Some(q1',qq1',aX') -> _q1 := q1'; _qq1 := qq1'; _aX := aX'
    end
  done;
  (!_q1,!_qq1,!_aX,!_q2,!_qq2,!_aY)
;;

let grouping pp qq1 qq2 =
  let aEmpty = ([],[]) in  
  let mkSeparategroups2 qq = List.map (fun q -> (pp,Path.dummy,aEmpty,q,aEmpty)) qq in
  let _grpL = ref [] in
  let _qq1 = ref qq1 in
  let _qq2 = ref qq2 in
  while !_qq1 <> [] do
    let q1a = List.hd !_qq1 in
    let qq1a = List.tl !_qq1 in
    let (q1',qq1',aX',q2',qq2',aY') = grouping_by_pingpong pp q1a qq1a aEmpty !_qq2 aEmpty in
    _qq1 := qq1';
    _qq2 := qq2';
    _grpL := (pp,q1',aX',q2',aY') :: !_grpL
  done;
  List_tailrec.append_rev !_grpL (mkSeparategroups2 !_qq2)
;;  

let biabduction pp ss1 ss2 = 
  let preciseflag = true in
  Ftools.pf_s tagDebug print_endline "[Biabduction Input]";
  Ftools.pf_s tagDebug print_endline ("P: " ^ P.to_string (P.And pp));
  Ftools.pf_s tagDebug print_endline ("A: " ^ SS.to_string ss1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ SS.to_string ss2);
  (* to path *)
  let _qq1 = ref (Paths.fromSpat ss1) in
  let _qq2 = ref (Paths.fromSpat ss2) in
  Ftools.pf_s tagDebug print_endline "[Transforming into paths]";
  Ftools.pf_s tagDebug print_endline ("A: " ^ Paths.to_string !_qq1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ Paths.to_string !_qq2);
  (* normalization *)  
  _qq1 := Paths.normalize pp !_qq1;
  _qq2 := Paths.normalize pp !_qq2;
  Ftools.pf_s tagDebug print_endline "[Normalization]";
  Ftools.pf_s tagDebug print_endline ("A: " ^ Paths.to_string !_qq1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ Paths.to_string !_qq2);
  (* rotate cycles *)
  let (qq1,qq2) = Paths.rotate_cycles pp !_qq1 !_qq2 in
  _qq1 := qq1;
  _qq2 := qq2;
  Ftools.pf_s tagDebug print_endline "[Rotate cycles]";
  Ftools.pf_s tagDebug print_endline ("A: " ^ Paths.to_string !_qq1);
  Ftools.pf_s tagDebug print_endline ("B: " ^ Paths.to_string !_qq2);

  let groupL = grouping pp !_qq1 !_qq2 in
  Ftools.pf_s tagDebug print_endline "[Grouping]";
  let _groupsolutionL = ref [] in
  for i = 0 to List.length groupL - 1 do
    let (_,q1,aX,q2,aY) = List.nth groupL i in
    let i' = string_of_int i in
    Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ "] q1: " ^ (Path.to_string q1));
    Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ "]  X: " ^ (BAsh.to_string aX));
    Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ "] q2: " ^ (Path.to_string q2));
    Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ "]  Y: " ^ (BAsh.to_string aY));
    let solutionL = biabduction_core preciseflag pp q1 aX q2 aY in
    doIfDebug
      (fun _ -> 
        for j = 0 to List.length solutionL - 1 do
          let j' = string_of_int j in
          let (aXj,aYj) = List.nth solutionL j in
          Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ ":" ^ j' ^ "] X: " ^ (BAsh.to_string aXj));
          Ftools.pf_s tagDebug print_endline ("[G" ^ i' ^ ":" ^ j' ^ "] Y: " ^ (BAsh.to_string aYj));
        done;
      ) ();
    _groupsolutionL := solutionL :: !_groupsolutionL;
  done;
  _groupsolutionL := List.rev !_groupsolutionL;

  Ftools.pf_s tagDebug print_endline "[Biabduction solutions]";  
  let xysolutionL = List_tailrec.allChoice !_groupsolutionL in
  let mkSolution pairL =
    let _aX = ref ([],[]) in
    let _aY = ref ([],[]) in
    for i = 0 to List.length pairL - 1 do
      let (aX,aY) = List.nth pairL i in
      _aX := BAsh.join !_aX aX;
      _aY := BAsh.join !_aY aY;      
    done;
    (!_aX,!_aY)
  in
  let solutionL = List.map mkSolution xysolutionL in
  doIfDebug 
    (fun _ ->
      for i = 0 to List.length solutionL - 1 do
        let i' = string_of_int i in
        let (a1,a2) = List.nth solutionL i in
        Ftools.pf_s tagDebug print_endline ("X" ^ i' ^ ": " ^ BAsh.to_string a1);
        Ftools.pf_s tagDebug print_endline ("Y" ^ i' ^ ": " ^ BAsh.to_string a2);
      done;
    ) ();
  List.map (fun (aX,aY) -> (BAsh.toSH' aX,BAsh.toSH' aY)) solutionL
;;


