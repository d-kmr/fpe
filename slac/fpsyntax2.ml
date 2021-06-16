open Tools;;
(* open Slsyntax;; *)

module C = Csyntax;;
module Kexp = Csyntax.Exp;;

               
module Val = struct

  type s =
    | Ph of bytes (* place holder *)
    | Sname of bytes (* struct name *)
    | Fname of bytes list (* func name list *)

  (* [v1;v2] means (v1 union v2) *)
  (* [] means "None" *)
  type t = s list

  let none = []
         
  let rec to_string v =
    match v with
    | [] -> "None"
    | [Ph p] -> p
    | _ -> string_of_list to_string1 "U" v
  and to_string1 u =
    match u with
    | Ph p -> p
    | Sname sname -> sname
    | Fname fnameL -> "{" ^ (string_of_list (fun x->x) "," fnameL) ^ "}"

  let rec print (v: t) =
    match v with
    | [] -> print_string' "None";
    | _ -> print_string' (to_string v)
  and print1 u =
    match u with
    | Ph p -> print_string' p;
    | Sname sname -> print_string' sname;
    | Fname fnameL -> print_string' "{"; print_list print_string' "," fnameL; print_string' "}"
      
  let println (v: t) = print v; print_endline ""

  let split (v: t) =
    let rec aux fnameL snameL phL v1 = 
    match v1 with
    | [] -> (fnameL,snameL,phL)
    | (Fname fnameL1)::v2 ->
       aux (Tools.union fnameL fnameL1) snameL phL v2
    | (Sname strName)::v2 ->
       aux fnameL (Tools.union snameL [strName]) phL v2
    | (Ph p)::v2 ->
       aux fnameL snameL (Tools.union phL [p]) v2
    in
    aux [] [] [] v

  let combine (fnameL,snameL,phL) : t =
    let fnameVal = if fnameL = [] then [] else [Fname fnameL] in
    fnameVal @ (List.map (fun s -> Sname s) snameL) @ (List.map (fun p -> Ph p) phL)

  let normalize (v: t) = combine (split v)
    
  let check (v: t) =
    let (fnameL,snameL,phL) = split v in
    match fnameL,snameL,phL with
    | _,_::_::_,_ ->
       print_string' "Incorrect value: "; println v;
       failwith "Val.check"
    | _::_,_::_,_ ->
       print_string' "Incorrect value: "; println v;
       failwith "Val.check"
    | _,_::_,_::_ ->
       print_string' "Incorrect value: "; println v;
       failwith "Val.check"
    | _ -> ()                   
    
  let getFname v =
    let (fnameL,_,_) = split v in
    fnameL

  let getSname loc v =
    let (_,snameL,_) = split v in
    match snameL with
    | [strName] -> strName
    | [] -> 
       C.print_error loc @@ "Val.getSname: " ^ (to_string v) ^ " is not struct name (skip with \"\")";
       ""
    | _ -> 
       C.print_error loc @@ "Val.getSname: " ^ (to_string v) ^ " has more than one struct names (skip with \"\")";
       ""
       
  let rec getPhL v =
    List.fold_left
      (fun pp u -> Tools.union pp (getPhL1 u))
      []
      v
  and getPhL1 u =
    match u with
    | Sname _ -> []
    | Fname _ -> []
    | Ph _ -> [u]

  let union (v1: t) (v2: t) : t =
    let (fnameL1,snameL1,phL1) = split v1 in
    let (fnameL2,snameL2,phL2) = split v2 in
    let fnameL = Tools.union fnameL1 fnameL2 in
    let snameL = Tools.union snameL1 snameL2 in
    let phL = Tools.union phL1 phL2 in
    let v = combine (fnameL,snameL,phL) in
    check v;
    v
                           
(*            
  let rec union loc (v1: t) (v2: t) : t =
    match v1,v2 with
    | None,_ -> v2
    | _,None -> v1
    | Fname [],_ -> v2
    | _,Fname [] -> v1
    | Fname fnameL1,Fname fnameL2 -> Fname (Tools.union fnameL1 fnameL2)
    | Sname sname1,Sname sname2 -> Sname sname2
    | Union vv1,Union vv2 -> Union (merge vv1 vv2)
    | Union vv,_ -> Union (merge vv [v2])
    | _,Union vv -> Union (merge [v1] vv)
    | Ph v1,Ph v2 when v1 = v2 -> Ph v1
    | Ph _,_ -> Union (merge [v1] [v2])
    | _,Ph _ -> Union (merge [v1] [v2])
    | _ -> raise Exit
  and merge vv1 vv2 : t list = 
    match vv1,vv2 with
    | [],_ -> vv2
    | _,[] -> vv1
    | hd1::vv1',hd2::vv2' when hd1 = hd2 -> hd1 :: (merge vv1' vv2')
    | (Fname fnameL1)::vv1',(Fname fnameL2)::vv2' -> (Fname (Tools.union fnameL1 fnameL2)) :: (merge vv1' vv2')
    | (Fname _)::vv1',hd::vv2' -> hd :: (merge vv1 vv2')
    | hd::vv1',(Fname _)::vv2' -> hd :: (merge vv1' vv2)
    | hd1::vv1',hd2::vv2' -> hd1 :: hd2 :: (merge vv1' vv2')
 *)

  (* substitution for place holders *)
  let rec subst (sub: (bytes * t) list) v =
    List.fold_left
      (fun v0 u ->
        let v1 = subst1 sub u in
        union v0 v1
      )
      []
      v
  and subst1 sub u =
    match u with
    | Ph p ->
       begin
         match List.assoc_opt p sub with
         | None -> [ Fname [] ] (* return {}, if [fp] is not defined *)
         | Some v -> v
       end
    | _ -> [u]
      
  let toBarVarName p = "[" ^ p ^ "]"

end
;;

module StoreHeap = struct

  (* shshshshsh *)
  type t = store * heap
  and storeFP = (bytes * Val.t) list
  (* s(fp) = {F1,..Fn} or s(fp) = varfp *)
  and storeRetFP = bytes list (* $retFP = {F1,F2} *)
  and storeRetStruct = bytes  (* $retST = structName *)
  and storeStack = (storeFP * storeRetFP * storeRetStruct) list
  and storeRetVal = Val.t 
  and store = storeStack * storeRetVal
  and heap = (bytes * Val.t) list V.t
  (* h(strName) = [ (f1,{func1,func2}); (f2,{func3}) ] *)
  (* h("") is h( * ) that means the value of *e of function pointer types *)

  (* pre-heap *)
  (* [ (strName1,[(f,{F1})]);(strName1,[(f,{F2})]);(strName2,[(g,{G})]) ] *)
  (* This is the return type of allocTypeFP *)
  type preheap = (bytes * ((bytes * Val.t) list)) list

  let preheap_empty = []

  let println_preheap (preheap: preheap) =
    print_list
      (fun (strName,cell) ->
        print_string' @@ strName ^ "->{";
        print_list (fun (f,v) -> print_string' (f ^ ":"); Val.print v) ";" cell;
        print_string' @@ "}"
      )
      " "
      preheap
                    
  let storeStack_of s = fst s

  let retVal_of s = snd s 
    
  let fp_of s = List.flatten @@ List.map fst3 (storeStack_of s)
                  
  let s_init retFP retStruct : store =
    let storeStack = [ ([],retFP,retStruct) ] in
    (storeStack,Val.none)

  let h_empty: heap = V.singleton "*" [("*",Val.none)]
    
  let sh_init retFP retStruct : t =
    let s = s_init retFP retStruct in
    let h = h_empty in
    (s,h)

  let dummy =
    let s0 = ([],Val.none) in
    let h0 = V.empty in
    (s0,h0)
    
  let resetReturn_s (s:store) : store =
    let (s_stack,s_retVal) = s in
    let (s_fp,_,_) = List.hd s_stack in
    let s_stack' = (s_fp,[],"") :: (List.tl s_stack) in
    (s_stack',s_retVal)

  let resetReturn (sh:t) : t =
    let (s,h) = sh in
    let s' = resetReturn_s s in
    (s',h)
    
  let checkStack (sh: t) =
    let (s,h) = sh in
    if storeStack_of s = [] then print_endline "NOOOOOOOOO" else print_endline "YESSSSSSSSSSSSSSSSSS"

  let rec print (sh: t) =
    let (s,h) = sh in
    print_s s; 
    print_string' " ";
    print_h h
  and print_s (s: store) =
    let (storeStack,storeRetVal) = s in
    print_string' "s:[ ";
    print_s_stack storeStack;
    print_string' "]";
  and print_s_stack storeStack =    
    let print_stack_one (storeFP,retFP,retStruct) =
      print_string' "(";
      print_s_fp storeFP;
      print_string' ";";
      print_string' (string_of_list (fun x->x) "," retFP);
      print_string' ";";
      print_string' retStruct;
      print_string' ")";
    in
    print_string' "[";
    print_list print_stack_one "," storeStack;
    print_string' "]"
  and print_s_fp s_fp =
    let print_f_one (fp,fpval) =
      print_string' @@ fp ^ "=";
      Val.print fpval;
    in
    print_list print_f_one "," s_fp
  and print_h_one strName fldValL =
    print_string' @@ strName ^ "=>(";
    print_list (fun (fld,v) -> print_string' (fld ^ ":" ^ (Val.to_string v))) "," fldValL;
    print_string' @@ ")"
  and print_h_one_fld strName fldValL fld =
    let value = List.assoc fld fldValL in
    print_string' @@ strName ^ "=>(.., ";
    print_string' @@ fld ^ ":" ^ (Val.to_string value);
    print_string' @@ " ,..)"
  and print_h h =
    print_string' @@ "h:[ ";
    print_V print_h_one "," h;
    print_string' @@ "]"

  let println (sh: t) = print sh; print_endline ""

  let println_s (s: store) = print_s s; print_endline ""

  let println_s_fp (s: store) = print_s_fp (fp_of s); print_endline ""
                       
  let println_h_one strName fldValL = print_h_one strName fldValL; print_endline ""
                           
  let println_h (h: heap) = print_h h; print_endline ""

  let println1_h (h: heap) strName =
    try
      print_h_one strName (V_mes.find "println1_h" strName h);
      print_endline ""
    with
      _ ->
       print_endline @@ strName ^ " is Not found";
       ()
                   
  let dom h = List.map (fun (id,_) -> (int_of_string id)) (V.bindings h)

  let heapsize h = List.length h

  let add_h (n,name,kk) h =
    V.add (string_of_int n) (name,kk) h

  let getRealStrName aliases strName =
    let rec aux prev cur =
      match V.find_opt cur aliases with
      | None -> cur
      | Some next when next = cur -> cur
      | Some next -> aux cur next
    in
    aux "" strName
                    
  (* h(strName) *)
  let lookup_h aliases (sh : t) strName =
    let realStrName = getRealStrName aliases strName in
    let (_,h) = sh in
    match V.find_opt realStrName h with
    | Some xx -> xx
    | None -> 
       print_endline @@ "lookup_h: Not_found " ^ realStrName;
       failwith ""
    
  (* h(strName)(fld) *)
  let lookup_h_field loc aliases (sh : t) strName fld e tp =
    let fldValL = lookup_h aliases sh strName in
    try
      List.assoc fld fldValL
    with
      Not_found ->
       let (outMes,outValue) = if Kexp.hasFunc tp
                               then ("{}", [ Val.Fname [] ])
                               else ("[]", Val.none)
       in
       outValue

  let lookup_h_field_fp loc aliases (sh : t) strName fld =
    let fldValL = lookup_h aliases sh strName in
    match List.assoc_opt fld fldValL with
    | None -> None      
    | Some v ->
       let (fnameL,snameL,phL) = Val.split v in
       if snameL <> []
       then
         begin
           print_endline @@ fld ^ " is not FP-field in " ^ strName;
           print_h_one_fld strName fldValL fld;
           print_endline "";
           None
         end         
       else Some v

  let lookup_h_field_str loc aliases (sh : t) strName fld =
    match List.assoc_opt fld (lookup_h aliases sh strName) with
    | None -> ""
    | Some v ->
       let (_,snameL,_) = Val.split v in
       match snameL with
       | [strName] -> strName
       | _ -> ""
       
  (* sh(fp) = {F1,..,Fn} (value) *)
  let evalVar_fp loc (sh: t) var =
    let (s,_) = sh in
    try
      List.assoc var (fp_of s)
    with
      Not_found ->
      C.print_warn loc @@ "evalVar_fp: " ^ var ^ " is missing (skip with {})";
      [Val.Fname []]
      
  let evalFP_s_opt loc (s: store) fp =
    try
      Some (List.assoc fp (fp_of s))
    with
      Not_found -> None

  (* sh(fp) = {F1,..,Fn} (bytes list) *)
  let evalFP loc (sh: t) fp : bytes list =
    let (s,_) = sh in
    try
      match List.assoc_opt fp (fp_of s) with
      | Some v ->
         let (fnameL,_,_) = Val.split v in
         fnameL
      | _ -> []
    with
      Not_found -> []
                 
  let rec evalCExpInt loc (sh: t) (exp: Kexp.t) : int =
    match exp with          
    | Kexp.Lval lval -> evalCExpInt_lval loc sh lval
    | Kexp.Int n -> n
    | Kexp.Op (op,e1,e2) ->
       let n1 = evalCExpInt loc sh e1 in
       let n2 = evalCExpInt loc sh e2 in
       begin
         match op with
         | Kexp.Add -> n1+n2
         | Kexp.Sub -> n1-n2
         | Kexp.Mul -> n1*n2
         | Kexp.Div -> n1/n2
         | Kexp.Mod -> n1 mod n2
         | _ ->
            C.print_warn loc @@ "evalCExpInt: unexpected case: " ^ (Kexp.to_string exp) ^ " (skip with 0)";
            0
       end
    | _ ->
       C.print_warn loc @@ "evalCExpInt: unexpected case: " ^ (Kexp.to_string exp) ^ " (skip with 0)";
       0
  and evalCExpInt_lval loc (sh: t) lval =
    match lval with
    | Kexp.Var (v,_) -> -2 (* missing value *)
    | _ ->
       C.print_warn loc @@ "evalCExpInt: unexpected case: " ^ (Kexp.to_string_lval lval) ^ " (skip with 0)";
       0

  (* sh(exp) = {f1,f2} or {} *)
  (* A non-fp expression may come. Then evalCExpFp returns [] *) 
  let rec evalCExpFp loc strV aliases funtable (sh: t) (exp: Kexp.t) : Val.t =
    match exp with
    | Kexp.Lval lval -> evalCExpFp_lval loc strV aliases funtable sh lval
    | Kexp.Func fname -> [Val.Fname [fname]]
    | Kexp.Int 0 -> Val.none
    | Kexp.Addr lval -> evalCExpFp_lval loc strV aliases funtable sh lval
    | _ -> Val.none
  and evalCExpFp_lval loc strV aliases funtable (sh: t) lval =
    match lval with
    | Kexp.Var (ret,tp) when ret = "$ret" ->
       let value = retVal_of (fst sh) in
       value
    | Kexp.Var (fname,tp) when V.mem fname funtable || Kexp.isFunType tp ->
       [Val.Fname [fname]]
    | Kexp.Var (fp,tp) when Kexp.isFpType tp ->
       let (s,_) = sh in
       begin       
         try
           List.assoc fp (fp_of s)
         with
           _ -> [Val.Fname []]
       end
    | Kexp.Var _ -> Val.none
    | Kexp.Ptr e ->
       begin
         match Kexp.getTrueType_opt strV aliases e with
         | Some tp when Kexp.isFpType tp ->
            begin
              (* getting fnameL from h("") = {"*":fnameL} *)
              match lookup_h_field_fp loc aliases sh "*" "*" with 
              | Some value -> value
              | _ -> Val.none
            end
         | _ ->
            evalCExpFp loc strV aliases funtable sh e
       end
    | Kexp.Arrow (e,tp,fld) ->
       let tp1 = if tp <> [] then tp else Kexp.getTp e in
       let (ptrL,_,_,structL,_,_) = Kexp.split_tp tp1 in
       begin
         match ptrL,structL with
         | _,[] -> Val.none
         | _,(Kexp.STRUCT strName)::_ ->
            let realStrName = getRealStrName aliases strName in
            lookup_h_field loc V.empty sh realStrName fld e []
         | _ -> Val.none
       end
    | _ -> Val.none

  let evalCExpFp_fnameL loc strV aliases funtable (sh: t) (exp: Kexp.t) =
    let value = evalCExpFp loc strV aliases funtable sh exp in
    Val.getFname value
         
  (* sh(t) = strName or "" *)                 
  let rec evalCExpStr loc aliases (sh: t) (exp: Kexp.t) : bytes =
    match exp with      
    (* sh(v) = s(v) *)
    | Kexp.Lval l -> evalCExpStr_lval loc aliases sh l
    (* sh(F) = F *)
    | Kexp.Func fname ->
       C.print_error loc ("Store.evalCExpStr: " ^ (Kexp.to_string exp) ^ " is not a struct name (skip with \"\")");
       ""
    | _ -> ""
   
  and evalCExpStr_lval loc aliases (sh: t) (lval: Kexp.lval) =
    match lval with
    (* sh(v) = s(v) *)
    | Kexp.Var (ret,tp) when ret = "$ret" ->
       let value = retVal_of (fst sh) in
       let strName = Val.getSname loc value in
       let realStrName = getRealStrName aliases strName in
       realStrName
    | Kexp.Var (v,tp) when Kexp.hasStruct tp ->
       let (_,_,_,structL,_,_) = Kexp.split_tp tp in
       let strName = (function Kexp.STRUCT strName -> strName | _ -> "") (List_mes.hd "evalCExpStr" structL) in
       let realStrName = getRealStrName aliases strName in
       realStrName
    (* sh(e->fld) *)
    | Kexp.Arrow (e,tp,fld) ->
       let tp1 = if tp <> [] then tp else Kexp.getTp e in
       let (ptrL,_,_,structL,_,_) = Kexp.split_tp tp1 in
       begin
         match ptrL,structL with
         | _,[] ->
               C.print_error loc @@ "evalCExpStr_lval: s(" ^ (Kexp.to_string_lval lval) ^ "->" ^ fld ^ ") with not struct (skip with \"\")";
               ""
         | [],_ ->
            C.print_error loc @@ "evalCExpStr_lval: " ^ (Kexp.to_string_lval lval) ^ " is not a pointer (skip with \"\")";
            ""
         | _::_,(Kexp.STRUCT strName)::_ ->
            let realStrName = getRealStrName aliases strName in
            begin
              let value = lookup_h_field loc V.empty sh realStrName fld e [] in
              let (_,snameL,_) = Val.split value in
              match snameL with
              | [sname] -> getRealStrName aliases sname
              | _ ->
                 C.print_error loc @@ "evalCExpStr_lval: " ^ (Kexp.to_string_lval lval) ^ "->" ^ fld ^ " is not a struct  (skip with \"\")";
                 ""
            end
         | _ ->
            C.print_error loc @@ "evalCExpFp_lval: unexpected input (skip with \"\")";
            ""            
       end
    | _ -> ""

  let update_by_preheap (h: heap) (prehp: preheap) : heap =
    (*
    let printlnCell cell =
      print_list (fun (f,v) -> print_string' ("("^f^","); Val.print v; print_string' ")") "," cell;
      print_endline ""
    in
     *)
    let upfun cell = function
      | None -> Some cell
      | Some cell1 ->
         let _c = ref [] in
         for i = 0 to List.length cell - 1 do
           let (f,v) = List.nth cell i in
           let v' = 
             match List.assoc_opt f cell1 with
             | None -> v
             | Some v1 -> Val.union v1 v
           in
           _c := (f,v') :: !_c
         done;
         Some !_c
    in
    List.fold_left
      (fun h1 (strName,cell) ->
        try
          V_mes.update strName (upfun cell) h1
        with
          _ ->
          print_endline @@ "Exception happened in update_by_preheap";
          print_endline @@ strName;
          println1_h h strName;
          failwith "update_by_preheap"
      )
      h
      prehp

  let rec update_by_preheap_sh (sh: t) prehp =
    let (s,h) = sh in
    let h' = update_by_preheap h prehp in
    let sh' = (s,h') in
    sh'
    
  let filter_s (s: store) v : store =
    let (s_stack,s_retVal) = s in
    let s_stack' =
      let (_,retFP,retStruct) = List_mes.hd "filter_s" s_stack in
      let s_fp' = List.filter (fun (v1,_) -> v1 = v) (fp_of s) in
      [(s_fp',retFP,retStruct)]
    in
    (s_stack',s_retVal)

  (* s[fp:= S] *)
  let updateFpFlag_s loc (s: store) fp value : store * bool =
    let (s_stack,s_retVal) = s in
    let rec updateStackFlag stack =
      match stack with
      | [(s_fp,retFP,retStruct)] ->
         let (s_fp',flag) = updateListOrderFlag order1 s_fp fp value in
         let stack' = [(s_fp',retFP,retStruct)] in
         (stack',flag)
      | (s_fp,retFP,retStruct)::stack' when List.mem fp (List.map fst s_fp) ->
         let (s_fp',flag) = updateListOrderFlag order1 s_fp fp value in
         let stack' = (s_fp',retFP,retStruct)::stack' in
         (stack',flag)
      | hd::stack1 ->
         let (stack1',flag) = updateStackFlag stack1 in
         let stack' = hd::stack1' in
         (stack',flag)
      | [] -> failwith ""
    in
    let (s_stack',flag) = updateStackFlag s_stack in
    let s' = (s_stack',s_retVal) in
    (s',flag)
      
  let updateFP_s loc s fp value : store =
    let (s1,_) = updateFpFlag_s loc s fp value in
    s1

  let updateFP loc sh fp value : t =
    let (s,h) = sh in
    let s1 = updateFP_s loc s fp value in
    (s1,h)

  let updateFP_many loc (sh: t) fpValL : t =
    List.fold_left
      (fun sh (fp,value) ->
        updateFP loc sh fp value
      )
      sh
      fpValL
    (*
    let _sh = ref sh in
    List.iter (fun (fp,value) -> _sh := updateFP loc !_sh fp value) fpValL;
    !_sh
     *)

  (* h[(strName,f):=value] *)
  (* FAIL if strName is not in dom(h) *)
  (* The value of f is updated by value if f is an existing field in h(strName) *)
  (* NOTE: (f,value) is added if f is not in h(strName) *)
  let update_h loc aliases (h: heap) strName f (value: Val.t) : heap =
    let realStrName = getRealStrName aliases strName in
    let upfun opt =
      match opt with
      | None -> (* when h(strName) is undefined *)
         C.print_error loc @@ "update_h: missing address: " ^ realStrName ^ " (skip)";
         None 
      | Some body -> (* when h(strName)= body *)
         let body1 = updateList body f value in
         Some body1
    in
    V_mes.update realStrName upfun h
    
  let updateRetVal_s loc (s: store) retVal : store =
    let (s_stack,_) = s in
    (s_stack,retVal)

  let updateRetVal loc (sh: t) retVal : t =
    let (s,h) = sh in
    let s1 = updateRetVal_s loc s retVal in
    (s1,h)
    
  (* s[fp += fnameL](fp) = s(fp) union fnameL  *)
  (* Changed: true *)
  (* Unchanged: false *)
  let updateUnionFpFlag_s loc (s: store) fp value : store * bool =
    match evalFP_s_opt loc s fp with
    | None ->
       updateFpFlag_s loc s fp value
    | Some value0 ->
       let value1 = Val.union value0 value in
       updateFpFlag_s loc s fp value1
    
  let updateUnionFp_s loc (s: store) fp value : store = fst (updateUnionFpFlag_s loc s fp value)

  let updateUnionFpFlag_h loc (h: heap) strName fld value : heap * bool =
    let _flag = ref false in
    let h' = 
      V_mes.update strName
        (function
         | None -> None
         | Some cells ->
            let f (fld1,val1) =
              if fld1 <> fld
              then (fld1,val1)
              else
                let value1 = Val.union val1 value in
                if value1 <> val1 
                then _flag := true
                else ();
                (fld,value1)
            in
            Some (List.map f cells)
        )
        h
    in
    (h',!_flag)

  let rec updateUnionFpFlag_sh loc (sh: t) strName fld value : t * bool =
    let (s,h) = sh in
    let (h',flag) = updateUnionFpFlag_h loc h strName fld value in
    let sh' = (s,h') in
    (sh',flag)
    
  let updateUnionFp_h loc (h: heap) strName fld value : heap = fst (updateUnionFpFlag_h loc h strName fld value)
      
  let updateRetUnionFP_s loc (s: store) fnameL : store =
    let (s_stack,s_retVal) = s in
    let (s_fp,s_retFP,s_retStruct) = List_mes.hd "updateRetUnionFP_s" s_stack in
    let stack1 = List.tl s_stack in    
    let s_retFP' = union fnameL s_retFP in
    let s_stack' = (s_fp,s_retFP',s_retStruct)::stack1 in
    let s' = (s_stack',s_retVal) in
    s'
    
  let updateRetStruct_s s tpRet =
    let (s_stack,s_retVal) = s in
    match Kexp.getStructNameL tpRet with
    | [] -> s
    | strName::_ -> 
       let (s_fp,s_retFP,_) = List_mes.hd "updateRetStruct_s" s_stack in
       let stack1 = List.tl s_stack in
       let s_stack' = (s_fp,s_retFP,strName)::stack1 in
       let s' = (s_stack',s_retVal) in
       s'

  let updateRetStruct (sh:t) tpRet : t =
    let (s,h) = sh in
    let s' = updateRetStruct_s s tpRet in
    (s',h)

(*
  let pop_s tp s : store =
    let (s_stack,_) = s in
    match s_stack with
    | [] -> failwith "pop_s"
    | (_,retFP,_)::s_stack' when Kexp.isFpType tp ->
       let s_retVal' = [ Val.Fname retFP ] in
       (s_stack',s_retVal')
    | (_,_,retStruct)::s_stack' when Kexp.isStructType tp ->
       let s_retVal' = [ Val.Sname retStruct ] in
       (s_stack',s_retVal')
    | _::s_stack' ->
       (s_stack',Val.none)

  let pop tp (sh: t) : t =
    let (s,h) = sh in
    let s' = pop_s tp s in
    (s',h)
 *)
          
  let push_s s =
    let (s_stack,_) = s in
    let s_stack' = ([],[],"") :: s_stack in
    (s_stack',Val.none)

  let push (sh: t) : t =
    let (s,h) = sh in
    let s' = push_s s in
    (s',h)
    
  let closing_s s : store =
    let (s_stack,_) = s in
    match s_stack with
    | [] ->
       failwith "closing_s: empty storestack"
    | (_,[],"")::s_stack' ->
       let retVal = Val.none in
       let s1 = (s_stack',retVal) in
       s1
    | (_,fnameL,"")::s_stack' ->
       let retVal = [ Val.Fname fnameL ] in
       let s1 = (s_stack',retVal) in
       s1
    | (_,[],retStruct)::s_stack' ->
       let retVal = [ Val.Sname retStruct ] in
       let s1 = (s_stack',retVal) in
       s1
    | (_,_,_)::_ ->
       failwith "closing_s: illegal return"

  let closing (sh: t) =
    let (s,h) = sh in
    let s' = closing_s s in
    (s',h)
    
  let isFP_s s fp = List.mem fp (List.map fst (fp_of s))

  let isFP sh fp = isFP_s (fst sh) fp

  let union loc (sh1: t) (sh2: t) : t =
    let (s1,h1) = sh1 in
    let (s2,h2) = sh2 in
    let (s_stack1,s_retVal1) = s1 in
    let (s_stack2,s_retVal2) = s2 in
    let (s_fp1,s_retFP1,s_retStruct1) = List_mes.hd "union of s" s_stack1 in
    let (s_fp2,s_retFP2,s_retStruct2) = List_mes.hd "union of s" s_stack2 in    
    let s_stack1a = List.tl s_stack1 in
    let s_fpA = List_tailrec.merge (fun val1 val2 -> Val.union val1 val2) s_fp1 s_fp2 in
    let s_fp' = List.sort (fun (a1,v1) (a2,v2) -> order1 a1 a2) s_fpA in
    let s_retFP' = union s_retFP1 s_retFP2 in
    let s_retStruct' = if s_retStruct1 = "" || s_retStruct2 = ""
                       then s_retStruct1 ^ s_retStruct2
                       else s_retStruct1
    in
    let s_retVal' = Val.union s_retVal1 s_retVal2 in
    let s_stack' = (s_fp',s_retFP',s_retStruct') :: s_stack1a in
    let s' : store = (s_stack',s_retVal') in
    let h' : heap =
      match V.is_empty h1,V.is_empty h2 with
      | true,_ -> h2
      | _,true -> h1
      | _,_ ->
         V.union (fun strName cell1 cell2 ->
             Some (List_tailrec.merge
                     (fun v1 v2 ->
                       try
                         Val.union v1 v2
                       with
                         _ ->
                         C.print_error loc @@ "FPsh.union: heap mismatch on " ^ strName;
                         print_string' "value1 ";
                         Val.println v1;
                         print_string' "value2 ";
                         Val.println v2;
                         println1_h h1 strName;
                         println1_h h2 strName;
                         failwith ""
                     )
                     cell1 cell2)
           ) h1 h2
    in
    (s',h')

end
;;

module State = struct

  type t = SH of StoreHeap.t | None

  let print r =
    match r with
    | SH sh -> StoreHeap.print sh
    | None -> print_string' "None"

  let println r = print r; print_endline ""

  let println' header r =
    match r with
    | None ->
       print_endline (header ^ "None")
    | SH (s,h) ->
       print_string' header;
       StoreHeap.print_s s;
       print_string' " ";
       StoreHeap.println_h h

  let resetReturn r =
    match r with
    | None -> None
    | SH sh -> SH (StoreHeap.resetReturn sh)

  let updateRetStruct r tpRet = 
    match r with
    | None -> None
    | SH sh -> SH (StoreHeap.updateRetStruct sh tpRet)
             
  let union loc r1 r2 =
    match r1,r2 with
    | None,_ -> r2
    | _,None -> r1
    | SH sh1,SH sh2 ->
       let sh = StoreHeap.union loc sh1 sh2 in
       SH sh

       (*
  let storeExcludeFp r fpL =
    match r with
    | None -> None
    | SH (s,h) ->
       let s1 = StoreHeap.storeExcludeFp s fpL in
       SH (s1,h)
        *)
       
end
;;
