open Tools;;

exception NotPresburger
;;

exception NotSanitary
(* 
This exception will be raised when the sanitary checker finds: 
ASSUMPTION: order over hat-variables names ("" is the special name)
    "" < "a" < "b" < .. < "#size"

hatName(t) 
-- ("",0) (if t does not contain hat-var) 
-- (<name>,0) (if t has only one hat-var named <name>)
-- (<name>,1) (if t has two hat-vars #size and <name>)
-- raise NotSanitary (otherwise)

(name1,flag1) < (name2,flag2) := name1 < name2 or (name1 = name2 && flag1 < flag2)

Comparing two terms with the following BAD situation
(1) BAD condition for t < u 
errHAT not (hatName(t) < hatName(u))
errQSN (x? in t && hatName(u) <> ("",0)) or (x? in u && hatName(t) <> ("",0))
errTLD (x@tilde in t && hatName(u) <> ("",0)) or (x@tilde in u && hatName(t) <> ("",0))

(2) BAD condition for t <= u 
errHAT not (hatName(t) <= hatName(u))
errQSN (x? in t && hatName(u) <> "") or (x? in u && hatName(t) <> "")
errTLD (x@tilde in t && hatName(u) <> "") or (x@tilde in u && hatName(t) <> "")

(3) BAD condition for t = u 
errHAT not (hatName(t) = hatName(u))
errQSN (x? in t && hatName(u) <> "") or (x? in u && hatName(t) <> "")
errTLD (x@tilde in t && hatName(u) <> "") or (x@tilde in u && hatName(t) <> "")
*)
;;

(*----------------------------------*)
(* Terms of Symbolic Heap			*)
(*----------------------------------*)
module SHterm = struct
(* Term expressions			*)
(* 't' is used for them			*)
(* 'tt' is used for a list of them	*)


(* 
From vcpBase
type attr = PTR | STRUCT of string | EXQ | ARRAY of int list | PARAM | PTRPTR | GLOBAL | HAT | BAR | EXTERN | PROTO | TILDE | CHECK | DOT | NESTED
Attributions kept in SHterm-data are 
- types: "ptr", "$<name>", "arr" ("$<name>" is "struct <name>")
- sorts: "hat", "bar", "tilde", "check", "dot"
*)
  type attr =
    | PTR | STRUCT of string | EXQ | ARRAY of int list | PARAM | PTRPTR | GLOBAL | SIMPLE of int
    | HAT | BAR | EXTERN | PROTO | FUNC | TILDE | CHECK | DOT | NESTED | QUESTION | DOTDOT | ACUTE | INDIRECT
  type t =
    | Var of string * attr list (* Var(x,[hat;ptr]) *)
    | Int of int
    | Add of t list
    | Sub of t list (* left-assoc minus *)
    | Mul of t * t
    | Div of t * t
    | Mod of t * t
    | Shr of t * t
    | Shl of t * t
    | Band of t * t
    | Bor of t * t
    | Bxor of t * t
    | Bnot of t
    | Fcall of bytes * t list (* function call *)
    | Offset of bytes * t
              
  let rec isCons t =
    match t with
    | Int _ -> true
    | Add tt
      | Sub tt -> List.for_all isCons tt
    | Mul(t1,t2)
      | Div(t1,t2)
      | Mod(t1,t2)
      | Shr(t1,t2)
      | Shl(t1,t2)
      | Band(t1,t2)
      | Bor(t1,t2)
      | Bxor(t1,t2) -> isCons t1 && isCons t2
    | Bnot t1 -> isCons t1
    | _ -> false

  let rec evalCons t =
    match t with
    | _ when not(isCons t) -> failwith "evalCons : non-constant"
    | Int n -> n
    | Add tt ->
       let nn = List.map evalCons tt in
       List.fold_right ( + ) nn 0
    | Sub tt -> 
       let nn = List.map evalCons tt in
       if nn = [] then 0 else 
       List.fold_left ( - ) (List.hd nn) (List.tl nn)
    | Mul(t1,t2) ->
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 * n2
    | Div(t1,t2) ->
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 / n2
    | Mod(t1,t2) -> 
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 mod n2
    | Shr(t1,t2) ->
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 lsr n2
    | Shl(t1,t2) -> 
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 lsl n2
    | Band(t1,t2) -> 
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 land n2
    | Bor(t1,t2) -> 
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 lor n2
    | Bxor(t1,t2) ->
       let n1,n2 = evalCons t1, evalCons t2 in
       n1 lxor n2
    | Bnot t1 ->
       let n1 = evalCons t1 in
       lnot n1
    | _ -> failwith "evalCons : never occur"

  let rec isPb t =
    match t with
    | Var _ -> true
    | Int _ -> true
    | Add tt -> List.for_all isPb tt
    | Sub tt -> List.for_all isPb tt
    | Mul (t1,t2) -> (isCons t1 && isPb t2) || (isCons t2 && isPb t1)
    | Div (t1,t2) 
      | Mod (t1,t2) 
      | Shr (t1,t2)
      | Shl (t1,t2) -> isPb t1 && isCons t2
    | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> (isCons t1 && isPb t2) || (isCons t2 && isPb t1)
    | Bnot t1 -> isPb t1
    | Fcall _ -> false
    | Offset _ -> false

  let checkPresburger t =
    if isPb t
    then ()
    else raise NotPresburger
      
               
  let hom f t =
    match t with
    | Add tt -> Add (List.map f tt)
    | Sub tt -> Sub (List.map f tt)
    | Mod (t1,t2) -> Mod(f t1,f t2)
    | Mul (t1,t2) -> Mul(f t1,f t2)
    | Div (t1,t2) -> Div(f t1,f t2)
    | Shr (t1,t2) -> Shr(f t1,f t2)
    | Shl (t1,t2) -> Shl(f t1,f t2)
    | Band (t1,t2) -> Band(f t1,f t2)
    | Bor (t1,t2) -> Bor(f t1,f t2)
    | Bxor (t1,t2) -> Bxor(f t1,f t2)
    | Bnot t1 -> Bnot (f t1)
    | Fcall (g,tt) -> Fcall (g,List.map f tt)
    | _ -> t

  let rec fv t = match t with
    | Var (v,_) -> [v]
    | Int _ -> []
    | Add tt
      | Sub tt
      | Fcall (_,tt) -> List.concat (List.map fv tt)
    | Mul (t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> union (fv t1) (fv t2)
    | Bnot t1 -> dropRed (fv t1)
    | Offset _ -> []

  let rec fv_t t = match t with
    | Var _ -> [t]
    | Int _ -> []
    | Add tt
      | Sub tt
      | Fcall (_,tt) -> List.concat (List.map fv_t tt)
    | Mul (t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> union (fv_t t1) (fv_t t2)
    | Bnot t1 -> dropRed (fv_t t1)
    | Offset _ -> []

  let rec isConst t = match t with
    | Var _ -> false
    | Int _ -> true
    | Add tt -> List.for_all isConst tt
    | Sub tt -> List.for_all isConst tt
    | Mul (t1,t2) -> (isConst t1) && (isConst t2)
    | _ -> false
               
  let getVarName t =
    match t with
    | Var (v,_) -> [v]
    | _ -> []
               
  (* About attributions *)
  let rec getAttrs t =
    match t with
    | Var (_,attrs) -> attrs
    | Add tt
      | Sub tt
      | Fcall (_,tt) -> unionL (List.map getAttrs tt)
    | Mul(t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> union (getAttrs t1) (getAttrs t2)
    | Bnot t1 -> getAttrs t1
    | _ -> []
         
  let isVarWithAttr t a = (* t is a variable of attribution a *)
    match t with
    | Var (_,attrs) -> List.mem a attrs
    | _ -> false

  let isVarWithName t name = (* t is a variable of name v *)
    match t with
    | Var (v,_) when v = name -> true
    | _ -> false

  let isHatVar t = isVarWithAttr t HAT

  (* it checks hat-vars except #size@hat *)
  let isHatVar' t = (isHatVar t) && (isVarWithName t "#size")

  let isDotVar t = isVarWithAttr t DOT
                 
  let isTildeVar t = isVarWithAttr t TILDE
                   
  let isBarVar t = isVarWithAttr t BAR
                 
  let isCheckVar t = isVarWithAttr t CHECK
                   
  let isIndirectVar t = isVarWithAttr t INDIRECT
                   
  let isBCDTVar t = (isBarVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t)

  let isHCDTVar t = (isHatVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t)
                  
  let isSignVar t = (isBarVar t) || (isCheckVar t) || (isDotVar t) || (isTildeVar t) || (isHatVar t)

  let isIndirectVar t = isVarWithAttr t INDIRECT

  let hasGlobal t = isVarWithAttr t GLOBAL
                      
  let isLocalHat t = isHatVar t && not (hasGlobal t)

  let isNotLocalHat t = not (isLocalHat t)
                      
  let rec getVarsByAttrs aa t =
    match t with
    | Var (v,attrs) when not(disjoint aa attrs) (* && Bytes.get v 0 <> '#' *) -> [t]
    | Add tt
      | Sub tt
      | Fcall (_,tt) -> unionL (List.map (getVarsByAttrs aa) tt)
    | Mul(t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> union (getVarsByAttrs aa t1) (getVarsByAttrs aa t2)
    | Bnot t1 -> getVarsByAttrs aa t1
    | _ -> []

  let getVarsByAttrsL aa tt = unionL (List.map (getVarsByAttrs aa) tt)

  (* #size@hat is not considered as a hat var *)
  let hatVars t = List.filter (fun t -> isHatVar t) (getVarsByAttrs [HAT] t)

  let hatVars' t = List.filter (fun t -> isHatVar' t) (getVarsByAttrs [HAT] t)                 
                
  let barVars t = getVarsByAttrs [BAR] t
                
  let bcdtVars t = getVarsByAttrs [BAR;CHECK;DOT;TILDE] t

  let hcdtVars t = getVarsByAttrs [HAT;CHECK;DOT;TILDE] t
                 
  let signVars t = getVarsByAttrs [HAT;BAR;CHECK;DOT;TILDE] t
           
  let hatVarsL tt = List.filter (fun t -> isHatVar t) (getVarsByAttrsL [HAT] tt)

  let hatVarsL' tt = List.filter (fun t -> isHatVar' t) (getVarsByAttrsL [HAT] tt)                   
                  
  let barVarsL tt = getVarsByAttrsL [BAR] tt
                  
  let bcdtVarsL tt = getVarsByAttrsL [BAR;CHECK;DOT;TILDE] tt

  let hcdtVarsL tt = getVarsByAttrsL [HAT;CHECK;DOT;TILDE] tt                   
                   
  let signVarsL tt = getVarsByAttrsL [BAR;CHECK;DOT;TILDE;HAT] tt

  let to_string_op t =
    match t with
    | Mul(_,_) -> " * "
    | Div(_,_) -> " / "                
    | Mod(_,_) -> " % "
    | Shr (_,_) -> ">>"
    | Shl (_,_) -> "<<"
    | Band (_,_) -> " band "
    | Bor (_,_) -> " bor "
    | Bxor (_,_) -> "^"
    | _ -> ""

  let rec to_string t =
    match t with
    | Var (v,attrs) ->
       let aa' = to_string_attrL attrs in
       v ^ "<" ^ aa' ^ ">"
    | Int n ->
       let ns = string_of_int n in
       if n >= 0 then ns else "("^ns^")"
    | Add tt -> string_of_list to_string "+" tt
    | Sub tt ->
       if tt = [] then "" else
         let hd = to_string (List.hd tt) in
         let tl = string_of_list to_string1 "-" (List.tl tt) in
         hd ^"-"^tl
    | Mul (t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> 
       let op = to_string_op t in
	   let t1' = to_string1 t1 in
       let t2' = to_string1 t2 in
       t1' ^ op ^ t2'
    | Bnot t1 -> "~" ^ (to_string1 t1)
    | Fcall (g,tt) ->
       let arg = string_of_list to_string "," tt in
       g ^ "(" ^ arg ^ ")"
    | Offset(strName,t0) ->
       "Offset(" ^ strName ^ "," ^ (to_string t0) ^ ")"
  and to_string1 t =
    match t with
    | Var _ | Int _ | Mul(_,_) | Mod(_,_) -> to_string t
    | _ -> "(" ^ (to_string t) ^")"
  and to_string_attr a =
    match a with
    | PTR -> "PTR"
    | STRUCT sname -> "STRUCT " ^ sname
    | EXQ -> "EXQ"
    | ARRAY nn -> "ARRAY[" ^ (string_of_list string_of_int "," nn) ^ "]"
    | PARAM -> "PARAM"
    | PTRPTR -> "PTRPTR"
    | GLOBAL -> "GLOBAL"
    | HAT -> "HAT"
    | BAR -> "BAR"
    | EXTERN -> "EXTERN"
    | PROTO -> "PROTO"
    | FUNC -> "FUNC"             
    | TILDE -> "TILDE"
    | CHECK -> "CHECK"
    | DOT -> "DOT"
    | NESTED -> "NESTED"
    | QUESTION -> "QUESTION"
    | DOTDOT -> "DOTDOT"
    | ACUTE -> "AQUTE"
    | SIMPLE n -> "SIMPLE(" ^ (string_of_int n) ^ ")"
    | INDIRECT -> "INDIRECT"
  and to_string_attrL aa = string_of_list to_string_attr "," aa
    
  let print t = print_string (to_string t)

  let println t = print_string ((to_string t)^"\n")

  let isPTR_attrL aa = List.mem PTR aa

  let getARRAYinfo_attr a =
    match a with
    | ARRAY nn -> nn
    | _ -> []
         
  let isARRAY_attr a = (getARRAYinfo_attr a <> [])

  let isARRAY_attrL aa = List.exists isARRAY_attr aa

  let getSIMPLEinfo_attr a =
    match a with
    | SIMPLE n -> [n]
    | _ -> []

  let rec getSIMPLEinfo t =
    let aa = getAttrs t in
    match List.flatten (List.map getSIMPLEinfo_attr aa) with
    | [] -> []
    | n::_ -> [n]
                       
  let getSTRUCTinfo_attr a =
    match a with
    | STRUCT sname -> [sname]
    | _ -> []
         
  let getSTRUCTinfo_attrL aa = List.flatten (List.map getSTRUCTinfo_attr aa)
         
  let isSTRUCT_attrL aa = (getSTRUCTinfo_attrL aa <> [])
                        
  let getTypes t aa =
    match isARRAY_attrL aa, isPTR_attrL aa, isSTRUCT_attrL aa with
    | true,false,false -> ["arr"]
    | true,_,_ -> raise (Error (to_string t ^ " has an illegal type: ARRAY + PTR/STRUCT"))
    | _,true,_ -> "ptr" :: (getSTRUCTinfo_attrL aa)
    | _,false,_ -> getSTRUCTinfo_attrL aa

  let getTypeInfo t =
    let attrs = getAttrs t in
    getTypes t attrs

  let checkTypeInfo attr =
    let dummy = Int 0 in
    try
      let _ = getTypes dummy attr in
      true
    with
      _ -> false

  let rec getStructName t =
    let aa = getAttrs t in
    getSTRUCTinfo_attrL aa

  let rec getHeadTerm t =
    match t with
    | Var (_,_) -> [t]
    | Add (Var(v,_) ::tt) when v = "#size" -> getHeadTerm (Add tt)
    | Add (t1::_) 
      | Sub (t1::_) -> getHeadTerm t1
      | _ -> []
    
  (* Sanitary Checking *)
(* 
    varProfile t
    (<name>, unlimited_flag)
    ("",0)      (t does not contain hat-var and is limited) 
    ("",1)      (t does not contain hat-var and is unlimited) 
    (<name>,0)  (t has only one hat-var named <name> and is limited)
    (<name>,1)  (t has two hat-vars #size and <name> and is unlimited)
    raise NotSanitary (otherwise) 
*)
  let varProfile t =
    let tHatNameL = List.flatten @@ List.map getVarName (hatVarsL [t]) in
    match setminus tHatNameL ["#size"] with
    | [] ->
       if getVarsByAttrsL [BAR;DOT;DOTDOT] [t] <> []
       then ("",0)
       else ("",1)
    | [name] ->
       let flag = if List.mem "#size" tHatNameL then 1 else 0 in
       (name,flag)
    | _ -> raise NotSanitary

  let print_vp vp =
    let (name,flag) = vp in
    let str = name ^ ": " ^ (if flag = 0 then "limited" else "unlimited") in
    print_endline str
         
  let checkSan t = let _ = varProfile t in ()
         
  let ( <|< ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    (*
    print_vp vp1; print_vp vp2;        
     *)    
    let cond1 = (vp1 = ("",1)) && ((fst vp2 <> "") || snd vp2 = 0) in
    let cond2 = (fst vp1 <> "") && (fst vp1 >= fst vp2) in
    cond1 || cond2

  let ( <|= ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    (*
    print_vp vp1; print_vp vp2;        
     *)
    let cond1 = (vp1 = ("",1)) && ((fst vp2 <> "") || snd vp2 = 0) in
    let cond2 = (fst vp1 <> "") && (fst vp1 > fst vp2) in
    cond1 || cond2

  let ( =|= ) t1 t2 =
    let vp1 = varProfile t1 in
    let vp2 = varProfile t2 in
    (*
    print_vp vp1; print_vp vp2;        
     *)
    let cond1 = (fst vp1 <> "") && (fst vp2 <> "") && (vp1 <> vp2) in
    let cond2 = (vp1 = ("",0)) && (fst vp2 <> "") in
    cond1 || cond2

  let checkSanCompare op t1 t2 =
    match op with
    | "EQ" -> if t1 =|= t2 then raise NotSanitary else ()
    | "LT" -> if t1 <|< t2 then raise NotSanitary else ()
    | "LE" -> if t1 <|= t2 then raise NotSanitary else ()
    | _ -> ()
         
  (* Substitution on terms *)
  let rec varRepl (repl : (string* string) list) t =
    match t with
    | Var (v,attrs) ->
       begin
	     match findItemOption v repl with
	     | Some w -> Var (w,attrs)
	     | None -> t
       end
    | _ -> hom (varRepl repl) t

  let rec subst (sub : (string * t) list) t =
    match t,sub with
    | _,[] -> t
    | Var (x,attrs),_ ->
       begin
         try
	       List.assoc x sub
         with Not_found -> t
       end
    | _,_ -> hom (subst sub) t

  let nf t = t (* temp. by adding mod 2018.06.25 *)

  let eq t1 t2 = (nf t1) = (nf t2)

  let evalUnderPmodel_op t =
    match t with
    | Mul(_,_) -> ( * )
    | Div(_,_) -> ( / )
    | Mod(_,_) -> (mod)
    | Shr (_,_) -> (lsl)
    | Shl (_,_) -> (lsr)
    | Band (_,_) -> (land)
    | Bor (_,_) -> (lor)
    | Bxor (_,_) -> (lxor)
    | _ -> failwith ""

  let rec evalUnderPmodel pmodel t : int =
    match t with
    | Var (v,_) -> List.assoc v pmodel
    | Int n -> n
    | Add ts ->
	   let nn = List.map (evalUnderPmodel pmodel) ts in
	   List.fold_right (+) nn 0
    | Sub ts ->
	   let nn = List.map (evalUnderPmodel pmodel) ts in
	   begin
	     match nn with
	     | [] -> 0
	     | k::kk -> List.fold_left (-) k kk
	   end
    | Mul (t1,t2)
      | Div (t1,t2)
      | Mod (t1,t2)
      | Shr (t1,t2)
      | Shl (t1,t2)
      | Band (t1,t2)
      | Bor (t1,t2)
      | Bxor (t1,t2) -> 
       let op = evalUnderPmodel_op t in
	   let n1 = evalUnderPmodel pmodel t1 in
       let n2 = evalUnderPmodel pmodel t2 in
       op n1 n2
    | Bnot t1 -> lnot (evalUnderPmodel pmodel t1)
    | Fcall _ -> failwith "evalUnderPmodel: fun.call cannot be evaluated"
    | Offset _ -> failwith "evalUnderPmodel: offset cannot be evaluated"
  (*  
    extract_nonPb _vv _eqlist replaces non-presburger terms of given input like
    (f(y) + g(x) * y + 1) 
    then
    (##0 + ##1 + 1) 
    then
    !_vv = [x; y; ##0; ##1]; ##2]
    !_eqlist = [(##1*y,##2); (g(x),##1); (f(y),##0)] 
    This mechanism will be useful for pure and spatial parts
   *)
  let extract_nonPb _vv _eqlist t =
    let header = "##" in
    _vv := union (fv t) !_vv; (* used vars *)
    let replace_term t = 
      try
        let v = List.assoc t !_eqlist in
        Var (v,[])
      with
        Not_found ->
        let v = genFreshVar header !_vv in
        _vv := v :: !_vv;
        _eqlist := (t,v) :: !_eqlist;
        Var(v,[])
    in
    let rec aux t0 =
      match t0 with
      | Var _ 
        | Int _ -> t0
      | Add tt ->
         let tt' = List.map aux tt in
         Add tt'
      | Sub tt ->
         let tt' = List.map aux tt in
         Sub tt'
      | Mul (t1,t2) ->
         begin
           match isConst t1, isConst t2 with
           | false,false -> replace_term t
           | _,_ ->
              let t1' = aux t1 in
              let t2' = aux t2 in
              Mul(t1', t2')
         end
      | Div (t1,t2)
        | Mod (t1,t2)
        | Shr (t1,t2)
        | Shl (t1,t2)
        | Band (t1,t2)
        | Bor (t1,t2)
        | Bxor (t1,t2) -> replace_term t
      | Bnot t1 -> replace_term t
      | Fcall _ -> replace_term t
      | Offset _ -> replace_term t
    in
    aux t

  (* denominator t is [u] if t is t'/u or t'%u. Otherwise [] *)
  (* This is used for biabduction *)
  let denominators t =
    let rec aux t' = 
      match t' with
      | Var _ | Int _ -> []
      | Add tt | Sub tt ->
         List.flatten @@ List.map aux tt
      | Mul (t1,t2) | Shr (t1,t2) | Shl (t1,t2) | Band (t1,t2) | Bor (t1,t2) | Bxor (t1,t2) ->
         let tt1 = aux t1 in
         let tt2 = aux t2 in
         union tt1 tt2
      | Div (t1,t2) | Mod (t1,t2) ->
         let tt1 = aux t1 in
         let tt2 = t2 :: (aux t2) in
         union tt1 tt2
      | Bnot t1 -> aux t1
      | Fcall _ -> []   (* Reason: Fcall is ignored in the biabuduction *)
      | Offset _ -> []  (* Reason: Offset is ignored in the biabuduction *)
    in
    aux t

end
;;

(* Short cuts for SHterms *)
module T = SHterm;;
let var v attrs = T.Var (v,attrs);;
let num n = T.Int n;;
let zero = num 0;;
let one = num 1;;
let ( +.+ ) t1 t2 = T.Add [t1;t2];;
let ( -.- ) t1 t2 = T.Sub [t1;t2];;
let ( *.* ) t1 t2 = T.Mul(t1,t2);;
let ( %.% ) t n = T.Mod(t,n);;

module Subst = struct 
  type t = (string * SHterm.t) list
end;;

(*--------------------------------*)
(* Pure Formulas                  *)
(* used for the pure-part of SH   *)
(* pure is no longer presburger   *)
(*--------------------------------*)
module SHpure = struct
  
  (* 'p' is used for them			*)
  (* (In,[t;a;b]) means "t in [a,b]"  *)
  (* (Out,[t;a;b]) means "t notin [a,b]"  *)
  (* (Disj,[a;b;c;d]) means "[a,b] and [c,d] are disjoint"  *)
  (* (Comm,[a;b;c;d]) means "[a,b] and [c,d] have a common element"  *)
  type op = Eq | Neq | Le | Lt | In | Out | Disj | Comm
                          
  (* Assumption: negations are already removed by de Morgan's law *)
  type t =
    | True (* true (it is used for SH with empty pure-part) *)
    | False
    | Atom of op * T.t list (* atomic formula *)
    | And of t list (* conjunction *)
    | Or of t list  (* disjunction *)
    | All of string list * t  (* universal *)
    | Ex of string list * t  (* existential *)

  (* this checks whether the given p is a presburger formula *)
  (* If it is then do nothing, else raise the NotPresburger exception *)
  let rec checkPresburger p =
    match p with
    | True | False -> ()
    | Atom (_,tt) -> List.iter T.checkPresburger tt 
    | And pp | Or pp -> List.iter checkPresburger pp
    | All (_,p) | Ex (_,p) -> checkPresburger p

  let rec dual p =
    match p with
    | True -> False
    | False -> True
    | And pp ->
       let pp' = List.map dual pp in
       Or pp'
    | Or pp ->
       let pp' = List.map dual pp in
       And pp'
    | All (vv,p) -> Ex (vv,dual p)
    | Ex (vv,p) -> All (vv,dual p)
    | Atom (op,tt) ->
       match op with
       | Eq -> Atom (Neq,tt)
       | Neq -> Atom (Eq,tt)
       | Le ->
          let t0 = List.nth tt 0 in
          let t1 = List.nth tt 1 in
          Atom (Lt,[t1;t0])
       | Lt ->
          let t0 = List.nth tt 0 in
          let t1 = List.nth tt 1 in
          Atom (Le,[t1;t0])
       | In -> Atom (Out,tt)
       | Out -> Atom (In,tt)
       | Disj -> Atom (Comm,tt)
       | Comm -> Atom (Disj,tt)
                  
  let rec fv p = match p with
    | True 
      | False -> []
    | Atom (_,tt) -> unionL (List.map T.fv tt)
    | And pp
      | Or pp -> unionL (List.map fv pp)
    | All (vv,p)
      | Ex (vv,p) -> setminus (fv p) vv

  (* This function returns free variables as terms *)
  (* It is used to obtain free *signed* variables, which are never quantified *)
  let rec fv_t p = match p with
    | True -> []
    | False -> []
    | Atom (_,tt) -> unionL (List.map T.fv_t tt)
    | And pp -> unionL (List.map fv_t pp)
    | Or pp -> unionL (List.map fv_t pp)
    | All (vv,p) -> fv_t p
    | Ex (vv,p) -> fv_t p
                 
  let hatVars p = dropRed @@ List.filter T.isHatVar (fv_t p)
                
  let hatVars' p = dropRed @@ List.filter T.isHatVar' (fv_t p)
                
  let barVars p = dropRed @@ List.filter T.isBarVar (fv_t p)

  let bcdtVars p = dropRed @@ List.filter T.isBCDTVar (fv_t p)

  let signVars p = dropRed @@ List.filter T.isSignVar (fv_t p)

  let rec to_string p = match p with
    | True -> "True"
    | False -> "False"
    | Atom(op,tt) ->
       begin
         match op with
         | Eq -> string_of_list T.to_string1 " = " tt
         | Neq ->
            if List.length tt = 2 then
	          let t0 = T.to_string (List.nth tt 0) in
	          let t1 = T.to_string (List.nth tt 1) in
	          t0 ^ " =/ " ^ t1
            else
              let tt' = string_of_list T.to_string1 " " tt in
	          "(=/ " ^ tt' ^ ")"
         | Lt -> string_of_list T.to_string1 " < " tt
         | Le -> string_of_list T.to_string1 " <= " tt
         | In ->
            let t0 = T.to_string (List.nth tt 0) in
            let t1 = T.to_string (List.nth tt 1) in
            let t2 = T.to_string (List.nth tt 2) in
            t0 ^ " in [" ^ t1 ^ "," ^ t2 ^ "]"
         | Out ->
            let t0 = T.to_string (List.nth tt 0) in
            let t1 = T.to_string (List.nth tt 1) in
            let t2 = T.to_string (List.nth tt 2) in
            t0 ^ " out [" ^ t1 ^ "," ^ t2 ^ "]"
         | Disj ->
            let t0 = T.to_string (List.nth tt 0) in
            let t1 = T.to_string (List.nth tt 1) in
            let t2 = T.to_string (List.nth tt 2) in
            let t3 = T.to_string (List.nth tt 3) in
            "[" ^ t0 ^ "," ^ t1 ^ "] disj [" ^ t2 ^ "," ^ t3 ^ "]"
         | Comm ->
            let t0 = T.to_string (List.nth tt 0) in
            let t1 = T.to_string (List.nth tt 1) in
            let t2 = T.to_string (List.nth tt 2) in
            let t3 = T.to_string (List.nth tt 3) in
            "[" ^ t0 ^ "," ^ t1 ^ "] comm [" ^ t2 ^ "," ^ t3 ^ "]"
       end
    | And pp -> string_of_list to_string1 " & " pp
    | Or pp -> string_of_list to_string1 " | " pp
    | All(vv,p) ->
       let p' = to_string1 p in
       if vv = [] then p' else
         let vv' = string_of_list (fun v -> v) "," vv in
         "All[" ^ vv' ^ "](" ^ p' ^ ")"
    | Ex(vv,p) ->
       let p' = to_string1 p in
       if vv = [] then p' else
         let vv' = string_of_list (fun v -> v) "," vv in
         "Ex[" ^ vv' ^ "](" ^ p' ^ ")"
  and to_string1 p = match p with
    | True -> "True"
    | False -> "False"
    | Atom(_,_) -> to_string p
    | And pp | Or pp ->
       let p' = to_string p in
       if List.length pp = 1 then p' else "(" ^ p' ^ ")"
    | All(vv,_) | Ex(vv,_) ->
       let p' = to_string p in
       if vv = [] then p' else "(" ^ p' ^ ")"

  let print (it : t) = print_string (to_string it)

  let println (it : t) = print_string ((to_string it)^"\n")

  let rec flatten conn (p : t) =
    match conn,p with
    | "and", And pp ->
       List.flatten @@ List.map (flatten "and") pp
    | "or", Or pp ->
       List.flatten @@ List.map (flatten "or") pp
    | _,_ -> [p]

  (* Sanitary checking  *)
  (* x@hat < x@hat+1 is sanitary *)
  (* x@hat = y@hat is not sanitary *)
  let checkSanAtom p =
    match p with
    | True | False -> ()
    | Atom (Disj,tt) ->
       let t0L = List.nth tt 0 in
       let t0R = List.nth tt 1 in
       let t1L = List.nth tt 2 in
       let t1R = List.nth tt 3 in
       T.checkSanCompare "LT" t0R t1L;
       T.checkSanCompare "LT" t1R t0L;
    | Atom (Neq,tt) -> 
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       T.checkSan t0;
       T.checkSan t1;
    | Atom (Eq,tt) -> 
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       T.checkSanCompare "EQ" t0 t1;
    | Atom (Lt,tt) ->
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       T.checkSanCompare "LT" t0 t1
    | Atom (Le,tt) ->
       let t0 = List.nth tt 0 in
       let t1 = List.nth tt 1 in
       T.checkSanCompare "LE" t0 t1       
    | Atom (_,_) -> ()
    | And pp -> ()
    | Or pp -> ()
    | All(_,p) -> ()
    | Ex(_,p) -> ()

  let update_checkSan p =
    let rec aux p0 = 
      match p0 with
      | And pp ->
         let pp' = List.map aux pp in
         And pp'
      | Or pp ->
         let pp' = List.map aux pp in
         Or pp'
      | All(vv,p) ->
         let p' = aux p in
         All(vv,p')
      | Ex(vv,p) ->
         let p' = aux p in
         Ex(vv,p')
      | _ -> (* Atoms *)
         try
           checkSanAtom p0; p0
         with
           NotSanitary -> False
    in
    aux p
    
  let rec varRepl repl (p : t) : t = match p with
    | True as q -> q
    | False as q -> q
    | Atom(op,tt) -> 
       let tt' = List.map (T.varRepl repl) tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map (varRepl repl) pp in
       And pp'
    | Or pp ->
       let pp' = List.map (varRepl repl) pp in
       Or pp'
    | All(vv,p) ->
       let p' = varRepl repl p in
       All(vv,p')
    | Ex(vv,p) ->
       let p' = varRepl repl p in
       Ex(vv,p') 

  let alpha_conv vv_avoid (p : t) =
    let _vv_avoid = ref vv_avoid in
    let _repl = ref [] in
    let genSafeVar v =
      if List.mem v !_vv_avoid
      then
        let v' = genFreshVar v !_vv_avoid in
        _vv_avoid := v' :: !_vv_avoid;
        _repl := (v,v') :: !_repl;
        v'
      else v
    in
    let rec alpha p = 
      match p with
      | True as q -> q
      | False as q -> q
      | Atom(op,tt) as q -> q
      | And pp -> 
         let pp' = List.map alpha pp in
         And pp'
      | Or pp -> 
         let pp' = List.map alpha pp in
         Or pp'
      | All(vv0,p0) ->
         let vv1 = List.map genSafeVar vv0 in
         let p1 = varRepl !_repl (alpha p0) in
         All(vv1,p1)
      | Ex(vv0,p0) ->
         let vv1 = List.map genSafeVar vv0 in
         let p1 = varRepl !_repl (alpha p0) in
         Ex(vv1,p1)         
    in
    alpha p
       
  let rec subst (sub : Subst.t) p =
    let vv_fv = fv p in
    let vv_sub = List.flatten @@ List.map (fun (v,t) -> v :: (T.fv t)) sub in
    let vv_avoid = union vv_fv vv_sub in
    let p1 = alpha_conv vv_avoid p in
    match p1 with
    | True as q -> q
    | False as q -> q
    | Atom(op,tt) -> 
       let tt' = List.map (T.subst sub) tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map (subst sub) pp in
       And pp'
    | Or pp ->
       let pp' = List.map (subst sub) pp in
       Or pp'
    | All(vv0,p0) ->
       let p2 = subst sub p0 in
       All(vv0,p2)            
    | Ex(vv0,p0) ->
       let p2 = subst sub p0 in
       Ex(vv0,p2)     
      
  let rec nf (p : t) : t = match p with
    | True as q -> q
    | False as q -> q
    | Atom(op,tt) -> 
       let tt' = List.map T.nf tt in
       Atom (op,tt')
    | And pp ->
       let pp' = List.map nf pp in
       And pp'
    | Or pp ->
       let pp' = List.map nf pp in
       Or pp'
    | All(vv,p) ->
       let p' = nf p in
       All(vv,p')
    | Ex(vv,p) ->
       let p' = nf p in
       Ex(vv,p')

  (* 
    extract_nonPb _vv _eqlist (x = f(y) + 3 & z = g(x)) 
    returns
    x = ##0 + 3 & z = ##1
    with
    !_vv = [x;y;z;##0;##1]
    !_eqlist = [ (f(y),##0); (g(x),##1) ]
   *)
  let extract_nonPb _vv _eqlist p =
    _vv := union (fv p) !_vv;
    let rec aux p0 =
      match p0 with
      | True
        | False -> p0
      | Atom (op,tt) ->
         let tt' = List.map (T.extract_nonPb _vv _eqlist) tt in
         Atom (op,tt')
      | And pp ->
         let pp' = List.map aux pp in
         And pp'
      | Or pp ->
         let pp' = List.map aux pp in
         Or pp'         
      | All (vv,p) ->
         _vv := vv @ !_vv;
         let p' = aux p in
         All (vv,p')
      | Ex (vv,p) ->
         _vv := vv @ !_vv;
         let p' = aux p in
         Ex (vv,p')
    in
    aux p

  let denominators p =
    let rec aux p' =
      match p' with
      | True
        | False -> []
      | Atom (_,tt) ->
         unionL (List.map T.denominators tt)
      | And pp 
        | Or pp ->
         unionL (List.map aux pp)
      | All (_,p)
        | Ex (_,p) ->
         aux p
    in
    aux p

  (* Assumption: a@hat < b@hat < c@hat *)
  (* Atom (Disj,[a@hat;a@hat+N;b@hat;b@hat+M]) is reduced to Atom(Lt,[a@hat+N; b@hat]) *)
  (* Or [ Atom(Lt,[a@hat+N;b@hat]); Atom(Lt,[b@hat+M;a@hat]) ] is reduced to Atom(Lt,[a@hat+N;b@hat]) *)
  let reduce_disjunctions p =
    let rec aux p' =
      match p' with
      | All (vv,p1) ->
         let p1' = aux p1 in
         All(vv,p1')
      | Ex (vv,p1) ->
         let p1' = aux p1 in         
         Ex(vv,p1')
      | And pp ->
         let pp' = List.map aux pp in
         And pp'
      | Or [ Atom(Lt,[u1;t2]); Atom(Lt,[u2;t1]) ] 
      | Atom (Disj,[t1;u1;t2;u2]) ->
         let hatVars1 = dropRed (T.hatVarsL' [t1;u1]) in
         let hatVars2 = dropRed (T.hatVarsL' [t2;u2]) in
         let hatVarNames1 = List.flatten (List.map T.getVarName hatVars1) in
         let hatVarNames2 = List.flatten (List.map T.getVarName hatVars2) in
         begin
           match hatVarNames1,hatVarNames2 with
           | [v1],[v2] when v1 < v2 -> Atom(Lt,[u1;t2])
           | [v1],[v2] -> Atom(Lt,[u2;t1])
           | _ -> p'
         end
      | Or pp ->
         let pp' = List.map aux pp in
         Or pp'
      | _ -> p'
    in
    aux p

end
;;

module P = SHpure;;

let ( =.= ) t1 t2 = P.Atom(P.Eq, [t1;t2]);;
let ( <.< ) t1 t2 = P.Atom(P.Lt, [t1;t2]);;
let ( <.> ) t1 t2 = P.Atom(P.Neq, [t1;t2]);;
let ( <.= ) t1 t2 = P.Atom(P.Le, [t1;t2]);;
let _In t t1 t2 = P.Atom(P.In, [t;t1;t2]);;
let _Out t t1 t2 = P.Atom(P.Out, [t;t1;t2]);;
let _Disj t1 u1 t2 u2 = P.Atom(P.Disj, [t1;u1;t2;u2]);;
let _Comm t1 u1 t2 u2 = P.Atom(P.Comm, [t1;u1;t2;u2]);;

let ( &.& ) p q = P.And [p;q];;
let ( |.| ) p q = P.Or [p;q];;
let _All vv p = P.All(vv,p);;
let _Ex vv p = P.Ex(vv,p);;


module SHspatExp = struct
(* Single Spatial expressions *)
(* 's' is used for them	*)

  type t =
    | Pto of T.t * (bytes * T.t) list
    | Arr of T.t * T.t
    | Str of T.t * T.t (* String Part *)
    | Ind of bytes * T.t list (* inductive predicates *)

  (* this checks whether the given s consists of presburger terms *)
  (* If it is then do nothing, else raise the NotPresburger exception *)
  let checkPresburger s =
    match s with
    | Pto (t,cc) ->
       let tt = t :: (List.map snd cc) in
       List.iter T.checkPresburger tt
    | Arr (t1,t2)
      | Str (t1,t2) -> (T.checkPresburger t1; T.checkPresburger t2)
    | Ind (p,tt) -> List.iter T.checkPresburger tt
           
  let mkFV termFV s = match s with
    | Pto(t,gg) ->
       let tt = List.map snd gg in
       let tt1 = t::tt in
       unionL (List.map termFV tt1)
    | Arr(t1,t2) ->
       let vv1 = termFV t1 in
       let vv2 = termFV t2 in
       union vv1 vv2
    | Str(t1,t2) ->
       let vv1 = termFV t1 in
       let vv2 = termFV t2 in
       union vv1 vv2
    | Ind(_,tt) ->
       unionL (List.map termFV tt)
      
  let fv = mkFV T.fv

  let fv_t = mkFV T.fv_t

  let addrs (s : t) = match s with
    | Pto(t,_) -> [t]
    | Arr(t,u) -> [t;u]
    | Str(t,u) -> [t;u]
    | Ind(_,tt) -> []
       
  let hatVars s = dropRed @@ List.filter T.isHatVar (fv_t s)

  let hatVars' s = dropRed @@ List.filter T.isHatVar' (fv_t s)
                
  let barVars s = dropRed @@ List.filter T.isBarVar (fv_t s)

  let bcdtVars s = dropRed @@ List.filter T.isBCDTVar (fv_t s)

  let signVars s = dropRed @@ List.filter T.isSignVar (fv_t s)

  let hatVarsAddr s = T.hatVarsL (addrs s)
      
  let barVarsAddr s = T.barVarsL (addrs s)

  let bcdtVarsAddr s = T.bcdtVarsL (addrs s)
                     
  let signVarsAddr s = T.signVarsL (addrs s)

  let to_string s = match s with
    | Pto(t,uu) ->
      let t' = T.to_string t in
      let uu' =
        let to_string_u (f1,t1) =
          let t1' = T.to_string t1 in
          if f1 = "" then t1' else f1 ^ ":" ^ t1'
        in
        string_of_list to_string_u ", " uu
      in
      t' ^ " -> (" ^ uu' ^ ")"
    | Arr(t1,t2) ->
      let t1' = T.to_string t1 in
      let t2' = T.to_string t2 in
      "Arr(" ^ t1' ^ ", " ^ t2' ^ ")"
    | Str(t1,t2) ->
      let t1' = T.to_string t1 in
      let t2' = T.to_string t2 in
      "Str(" ^ t1' ^ ", " ^ t2' ^ ")"
    | Ind(p,tt) ->
       let tt' = string_of_list T.to_string "," tt in
       p ^ "(" ^ tt' ^ ")"
       
  let print (s : t) = print_string (to_string s)
    
  let println (s : t) = print_string ((to_string s)^"\n")

  let cells (s : t) = match s with
    | Pto(t,_) -> [t]
    | Arr(t,_) -> [t]
    | Str(t,_) -> [t]
    | Ind(_,_) -> []
                
  let getPtoContent (s : t) = match s with
    | Pto(_,cc) -> cc
    | _ -> []

  (* mkContentPairs [(f1:x1; f2:y1; f3:z1)] [(g2:a;f1:b;f2:c)] returns *)
  (* - [(f1,x1,b);(f2,y1,c)] *)
  let mkContentPairs cc1 cc2 =
    let compare_f c1 c2 = compare (fst c1) (fst c2) in
    let cc1' = List.sort compare_f cc1 in
    let cc2' = List.sort compare_f cc2 in
    let rec mkPairs res cc1a cc2a =
      match cc1a,cc2a with
      | _,[] -> res
      | [],_ -> res               
      | (f1,_)::cc1a',(f2,_)::_ when f1 < f2 -> mkPairs res cc1a' cc2a
      | (f1,_)::_,(f2,_)::cc2a' when f1 > f2 -> mkPairs res cc1a cc2a'
      | (f1,u1)::cc1a',(f2,u2)::cc2a' -> mkPairs ((u1,u2)::res) cc1a' cc2a'
    in
    mkPairs [] cc1' cc2'

  let getArraySeg (s : t) = match s with
    | Arr(t1,t2) -> [(t1,t2)]
    | _ -> []      

  let getStringSeg (s : t) = match s with
    | Str(t1,t2) -> [(t1,t2)]
    | _ -> []      

  let mkInterval (s : t) = match s with
    | Pto(t,_) -> (t,t)
    | Arr(t1,t2) -> (t1,t2)
    | Str(t1,t2) -> (t1,t2)
    | _ -> failwith "mkInterval: inductive predicate"
       
  let getArrayLen (s : t) = match s with
    | Arr(t1,t2) -> [T.Sub[t2;t1]]
    | _ -> []

  let getStringLen (s : t) = match s with
    | Str(t1,t2) -> [T.Sub[t2;t1]]
    | _ -> []

  let rec cellSize (s : t) = match s with
    | Pto(t,_) -> one
    | Arr(t1,t2) -> (t2 -.- t1) +.+ one
    | Str(t1,t2) -> (t2 -.- t1) +.+ one
    | _ -> failwith "cellSize: inductive predicate"
       
  let varRepl repl (s : t) : t = match s with
    | Pto(t,uu) ->
      let t' = T.varRepl repl t in
      let uu' = List.map (fun (f,t) -> (f, T.varRepl repl t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.varRepl repl t1 in
      let t2' = T.varRepl repl t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.varRepl repl t1 in
      let t2' = T.varRepl repl t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map (T.varRepl repl) tt in
       Ind(p,tt')

  let subst sub s = match s with
    | Pto(t,uu) ->
      let t' = T.subst sub t in
      let uu' = List.map (fun (f,t) -> (f,T.subst sub t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.subst sub t1 in
      let t2' = T.subst sub t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.subst sub t1 in
      let t2' = T.subst sub t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map (T.subst sub) tt in
       Ind(p,tt')
       
  let nf (s : t) : t = match s with
    | Pto(t,uu) ->
      let t' = T.nf t in
      let uu' = List.map (fun (f,t) -> (f,T.nf t)) uu in
      Pto(t',uu')
    | Arr(t1,t2) ->
      let t1' = T.nf t1 in
      let t2' = T.nf t2 in
      Arr(t1',t2')
    | Str(t1,t2) ->
      let t1' = T.nf t1 in
      let t2' = T.nf t2 in
      Str(t1',t2')
    | Ind(p,tt) ->
       let tt' = List.map T.nf tt in
       Ind(p,tt')
       
  let eq s1 s2 = (nf s1) = (nf s2)
      
  let checkSan s =
    match s with
    | Pto(t,cc) -> List.iter T.checkSan (t :: (List.map snd cc))
    | Arr(t1,t2) | Str(t1,t2) ->
       T.checkSan t1;
       T.checkSan t2
    | Ind (_,tt) ->
       List.iter T.checkSan tt
  (* 
    extract_fcall _vv _eqlist Arr(f(x),z)
    returns
    Arr(##0,z)
    with
    !_vv = [x;z;##0]
    !_eqlist = [ (f(x),##0) ]
   *)
  let extract_nonPb _vv _eqlist s =
    _vv := union (fv s) !_vv;
    let rec aux s0 =
      match s0 with
      | Pto (t,cc) ->
         let t' = T.extract_nonPb _vv _eqlist t in
         let cc' = List.map (fun (f,t) -> (f,T.extract_nonPb _vv _eqlist t)) cc in
         Pto (t',cc')
      | Arr (t1,t2) ->
         let t1' = T.extract_nonPb _vv _eqlist t1 in
         let t2' = T.extract_nonPb _vv _eqlist t2 in
         Arr (t1',t2')
    | Str (t1,t2) ->
         let t1' = T.extract_nonPb _vv _eqlist t1 in
         let t2' = T.extract_nonPb _vv _eqlist t2 in
         Str (t1',t2')
    | Ind (p,tt) ->
       let tt' = List.map (T.extract_nonPb _vv _eqlist) tt in
       Ind (p,tt')
    in
    aux s

  let denominators s =
    match s with
    | Pto (t,cc) ->
       let tt1 = T.denominators t in
       let tt2 = List.flatten @@ List.map (fun (_,t) -> T.denominators t) cc in
       union tt1 tt2
    | Arr (t1,t2)
      | Str (t1,t2) ->
       let tt1 = T.denominators t1 in
       let tt2 = T.denominators t2 in
       union tt1 tt2
    | Ind (_,tt) ->
       List.flatten @@ List.map T.denominators tt

  let getLsEndpoints s =
    match s with
    | Ind ("Ls",tt) -> tt
    | _ -> []

  (* Just checking "next"-field *)
  let isListPto s =
    match s with
    | Pto (_,cc) -> List.mem "next" (List.map fst cc)
    | _ -> false
    
end
;;

(* Short cuts for SHspatExps *)
module S = SHspatExp;;
let arr(t1,t2) = S.Arr(t1,t2);;
let str(t1,t2) = S.Str(t1,t2);;
let ( -.> ) t cc = S.Pto(t,cc);;
  


module SHspat = struct
(* 'ss' is used for them,		*)
(* since it is a list of single spat	*)

  type t = SHspatExp.t list

  let checkPresburger ss = List.iter S.checkPresburger ss
                         
  let fv (ss : t) = List.concat (List.map SHspatExp.fv ss)

  let fv_t (ss : t) = List.concat (List.map SHspatExp.fv_t ss)
                  
  let to_string (ss : t) =
    match ss with
    | [] -> "Emp"
    | _ -> string_of_list SHspatExp.to_string " * " ss
    
  let print ss = print_string (to_string ss)

  let println ss = print_string ((to_string ss)^"\n")

  let cells (ss : t) = unionL (List.map SHspatExp.cells ss)

  let addrs (ss : t) = unionL (List.map SHspatExp.addrs ss)
	  
  let split (ss : t) =
    let rec splitRec ptos arys strs inds ss1 =
      match ss1 with
      | [] -> (List.rev ptos,List.rev arys,List.rev strs,List.rev inds)
      | s'::ss' ->
	     match s' with
	     | S.Pto(_,_) -> splitRec (s'::ptos) arys strs inds ss'
	     | S.Arr(_,_) -> splitRec ptos (s'::arys) strs inds ss'
	     | S.Str(_,_) -> splitRec ptos arys (s'::strs) inds ss'
         | S.Ind(_,_) -> splitRec ptos arys strs (s'::inds) ss'
    in splitRec [] [] [] [] ss

  let getArraySeg (ss : t) = 
    List.concat (List.map SHspatExp.getArraySeg ss)

  let getStringSeg (ss : t) = 
    List.concat (List.map SHspatExp.getStringSeg ss)

  let mkSegment (ss : t) = List.map S.mkInterval ss
    
  let cellSize (ss : t) =
    T.Add (List.map SHspatExp.cellSize ss)
      
  let getArrayLen (ss : t) =
    List.concat (List.map SHspatExp.getArrayLen ss)

  let getStringLen (ss : t) =
    List.concat (List.map SHspatExp.getStringLen ss)
    
  let varRepl repl (ss : t) : t =
    List.map (SHspatExp.varRepl repl) ss

  let spat_length ss = List.length ss 
      
  let subst (sub : Subst.t) (ss : t) : t =
    List.map (SHspatExp.subst sub) ss

  let nf (ss : t) : t =
    List.map SHspatExp.nf ss

  let checkSan (ss : t) = List.iter S.checkSan ss

  (* lifting "f : S.t -> 'a list" to "(lift f) : SS.t -> 'a list" *)
  let lift sListFunc (ss : t) = unionL (List.map sListFunc ss)

  let hatVars = lift S.hatVars

  let hatVars' = lift S.hatVars'              

  let barVars = lift S.barVars

  let bcdtVars = lift S.bcdtVars
    
  let signVars = lift S.signVars
                        
  let hatVarsAddr = lift S.hatVarsAddr

  let barVarsAddr = lift S.barVarsAddr

  let bcdtVarsAddr = lift S.bcdtVarsAddr

  let signVarsAddr = lift S.signVarsAddr

  (* checkTypeConsistency ss *)
  (* It checks that ss has a consistent typeinfo as one memory block *)
  (* That is, ss should have the same type *)
  let checkTypeConsistency (ss : t) =
    let tt = List.flatten @@ List.map S.addrs ss in
    let attrs = unionL (List.map T.getAttrs tt) in
    T.checkTypeInfo attrs

  let extract_nonPb _vv _eqlist ss =
    List.map (S.extract_nonPb _vv _eqlist) ss

  let denominators ss = unionL (List.map S.denominators ss)

  (* t->(f:x<INDIRECT>,f1:t1) * x->( *:u) =>  t->(f:in(u,x<INDIRECT>),f1:t1) *)
  let fold_indirect (ss: t) : t =
    let isIndirectL s =
      match s with
      | S.Pto(t,_) when T.isIndirectVar t -> true (* x<INDIRECT> -> ( *:u) *)
      | _ -> false
    in
    let (ssIndirectL,ss1) = List_tailrec.splitLst isIndirectL ss in
    let indirectpairL = List.map
                      (fun s ->
                        match s with
                        | S.Pto(t,[(_,u)]) -> (T.getVarName t,u)
                        | _ -> failwith ""
                      )
                      ssIndirectL
    in
    let substC (f,t) =
      match T.isIndirectVar t with
      | false -> (f,t)
      | true ->
         let v = T.getVarName t in
         let u = List.assoc v indirectpairL in
         let in_u = T.Fcall ("#IN",[u;t]) in
         (f,in_u)
    in
    let substCC cc = List.map substC cc in
    let substCC_s s =
      match s with
      | S.Pto(t,cc) -> S.Pto(t,substCC cc)
      | _ -> s
    in
    List.map substCC_s ss1

  (* t->(f:in(u,x<INDIRECT>),f1:t1) => t->(f:x<INDIRECT>,f1:t1) * x->( *:u) *)
  let unfold_indirect (ss : t) : t =
    let unfold_c c =
      let (f,t) = c in
      match t with
      | T.Fcall("#IN",u :: xINDIRECT :: _) ->
         let s1 = S.Pto(xINDIRECT,[("*",u)]) in
         let c1 = (f,xINDIRECT) in
         (c1,[s1])
      | _ -> (c,[])
    in
    let unfold_s s =
      match s with
      | S.Pto(t,cc) ->
         let csL = List.map unfold_c cc in
         let cc1 = List.map fst csL in
         let ss1 = List.flatten (List.map snd csL) in
         let s1 = S.Pto(t,cc1) in
         s1 :: ss1
      | _ -> [s]
    in
    List.flatten (List.map unfold_s ss)

  (* Splitting of spatial part *)
  (* (ssArr,ssLs) *)
  (* Ex. Arr(x,y)*Ls(a,b) becomes (Arr(x,y),Ls(x,y))  *)
  let splitArrayList (ss : t) : t * t = 
    let (ssPto,ssArr,ssStr,ssLs) = split ss in
    let (ssLsPto,ssArrPto) = List_tailrec.splitLst S.isListPto ssPto in
    let ssArr1 = ssArrPto @ ssArr @ ssStr in
    let ssLs1 = ssLsPto @ ssLs in
    (ssArr1,ssLs1)
    
end
;;

module SS = SHspat
;;

(*------------------------------*)
(* Symbolic Heaps				*)
(*------------------------------*)
module SH = struct
(* 'h' is used for them			*)

  (* (vv,ppp,ss) means (Ex vvv.(pb & ss) *)
  type t = string list * SHpure.t * SHspat.t 

  let checkPresburger h =
    let (p,ss) = h in
    P.checkPresburger p;
    SS.checkPresburger ss
         
  let to_string (h : t) = 
    let (vv,p,ss) = h in
    let pS = P.to_string p in
    let ssS = SS.to_string ss in
    let vvS = string_of_list (fun x->x) "," vv in
    let addEx body =
      if vv = [] then body else "Ex " ^ vvS ^ ". " ^ body in
    match p,ss with
    | P.True,[] -> addEx "Emp"
    | _,[] -> addEx (pS ^ " & " ^ "Emp")
    | P.True,_ -> addEx ssS
    | _,_ -> addEx (pS ^ " & " ^ ssS)

  let print (h : t) = print_string (to_string h)
    
  let println (h : t) = print_string ((to_string h)^"\n")

  let av (h : t) =
    let (vv,p,ss) = h in
    let pV = P.fv p in
    let ssV = SS.fv ss in
    unionL [vv;pV;ssV]

  let bv (h : t) = let (vv,_,_) = h in vv

  let fv (h : t) =
    let hAV = av h in
    let hBV = bv h in
    List.filter (fun x -> not (List.mem x hBV)) hAV

  let of_spat (h : t)  = thd3 h

  let of_pure (h : t)  = snd3 h

  let cells (h : t) = SS.cells (of_spat h)

  let varRepl repl (h : t) : t =
    let (vv,p,ss) = h in
    let p1 = SHpure.varRepl repl p in
    let ss1 = SHspat.varRepl repl ss in
    (vv,p1,ss1)

  let spat_length (h : t) =
    let (_,_,ss) = h in
    SS.spat_length ss
      
  (* alpha_conv vars ([x;y],Pi,Sg)			*)
  (* it produces fresh variables x' and y'		*)
  (* where x' and y' are fresh for vars			*)
  (* Then returns ([x';y'],Pi[x'/x,y'/y],Sg[x'/x,y'/y])	*)
  let alpha_conv vars (h : t) : t = 
    let (vv,p,ss) = h in
    let rec alp_conv1 resbv vv1 p1 ss1 = 
      match vv1 with
      | [] -> (List.rev resbv,p1,ss1)
      | v::vv2 ->
	 if not(List.mem v vars) then alp_conv1 (v::resbv) vv2 p1 ss1
	 else
	   let v' = genFreshVar v vars in
	   let p2 = P.varRepl [(v,v')] p1 in
	   let ss2 = SS.varRepl [(v,v')] ss1 in
	   alp_conv1 (v'::resbv) vv2 p2 ss2
    in alp_conv1 [] vv p ss

  let subst (sub : Subst.t) (h : t) =
    let vvFV = fv h in
    let sub' = List.filter (fun (v,_) -> List.mem v vvFV) sub in
    let tt = List.map (fun (_,u)->u) sub' in
    let vars = List.concat (List.map T.fv tt) in
    let (vv1,p1,ss1) = alpha_conv vars h in
    let p2 = P.subst sub' p1 in
    let ss2 = SS.subst sub' ss1 in
    (vv1,p2,ss2)

  let nf (h : t) : t =
    let (vv,p,ss) = h in
    let p' = P.nf p in
    let ss' = SS.nf ss in
    (vv,p',ss')

  let extract_fcall _vv _eqlist (h : t) =
    let (vv,p,ss) = h in
    _vv := vv @ !_vv;
    let p' = P.extract_nonPb _vv _eqlist p in
    let ss' = SS.extract_nonPb _vv _eqlist ss in
    (vv,p',ss')

end
;;

(*--------------------------------------*)
(* Quantifier-Free Symbolic Heaps		*)
(*--------------------------------------*)
module QFSH = struct
(* 'k' is used for them			*)

  (* (ppp,ss) means (ppp & ss) *)
  type t = SHpure.t * SHspat.t 

  let up (k : t) : SH.t =
    let (p,ss) = k in
    ([],p,ss)

  let down (h : SH.t) : t =
    let (_,p,ss) = h in
    (p,ss)    

  let upfunc f = fun k -> f (up k)
      
  let to_string = upfunc SH.to_string
  let print = upfunc SH.print
  let println = upfunc SH.println
  let av = upfunc SH.av
  let bv = upfunc SH.bv
  let fv = upfunc SH.fv
  let of_spat = upfunc SH.of_spat
  let of_pure = upfunc SH.of_pure
  let spat_length = upfunc SH.spat_length
  let cells = upfunc SH.cells
  let subst sub k = down (SH.subst sub (up k))
  let nf k = down (SH.nf (up k))

  let checkPresburger k =
    let (p,ss) = k in
    P.checkPresburger p;
    SS.checkPresburger ss
           
  let getArrayLen (k : t) =
    let (_,ss) = k in
    SHspat.getArrayLen ss

  let isPtoHeadForm (k : t) =
    let (_,s) = k in
    match s with
    | S.Pto(_,_)::_ -> true
    | _ -> false

  let isArrHeadForm (p,s) =
    match s with
    | S.Arr(_,_)::_ -> true
    | _ -> false

  let extract_nonPb _vv _eqlist (k : t) =
    let (p,ss) = k in
    let p' = P.extract_nonPb _vv _eqlist p in
    let ss' = SS.extract_nonPb _vv _eqlist ss in
    (p',ss')

  let update_checkSan (k : t) =
    let (p,ss) = k in
    let p' = P.update_checkSan p in
    try
      SS.checkSan ss;
      (p',ss)
    with
      NotSanitary -> (P.False,[])
                   
end
;;

(* Module of Multi-conclusion Entailments *)  
module Entl = struct

(* Entailment has the form sh1 |- sh21 | sh22 | ... | sh2m *)
(* Basically, the quantifier-part of lhs is assumed to be empty *)
(* ([],P,S) |- (v1,P1,S1),...,(vn,Pn,Sn)	*)
(* 'e' is used for them *)

  type t = SH.t * SH.t list

  let to_string (e : t) =
    let (h,hh) = e in
    let hS = SH.to_string h in
    let hhS = string_of_list SH.to_string " | " hh in
    hS^" |- "^hhS

  let print (e : t) = print_string (to_string e)

  let println (e : t) = print_string ((to_string e)^"\n")

  let alpha_conv (e : t) : t =
    let open List_tailrec in
    let (h,hh) = e in
    let hh0 = h::hh in
    let rec alpha_conv_lst rest hh1 =
      match hh1 with
      | [] -> 
	let h2 = List.hd (List.rev rest) in
	let hh2 = List.tl (List.rev rest) in
	(h2,hh2)
      | h3::hh3 ->
	let vvFV = SH.fv h3 in
	let vvAV = List.concat (List.map SH.av (rest@hh3)) in
	let vv3 = union vvFV vvAV in
	let h4 = SH.alpha_conv vv3 h3 in
	alpha_conv_lst (h4::rest) hh3
    in alpha_conv_lst [] hh0

  let size (e : t) =
    let (h,hh) = e in
    let n = SH.spat_length h in
    let nn = List.map SH.spat_length hh in
    (n,nn)

  let string_of_size (e : t) =
    let (n,nn) = size e in
    let v = string_of_int n in
    let vv = string_of_list string_of_int "," nn in
    "("^v^", ["^vv^"])"
      
  let nf (e : t) : t =
    let (h,hh) = e in
    let h1 = SH.nf h in
    let hh1 = List.map SH.nf hh in
    alpha_conv (h1,hh1)
    
end
;;

(* Module of QF Multi-conclusion Entailments *)  
module QFEntl = struct
    
  type t = QFSH.t * QFSH.t list
    
  let up (e : t) =
    let (k,kk) = e in
    let h = QFSH.up k in
    let hh = List.map QFSH.up kk in
    (h,hh)

  let down (e : Entl.t) : t =
    let (h,hh) = e in
    let k = QFSH.down h in
    let kk = List.map QFSH.down hh in
    (k,kk)    

  let upfunc f = fun k -> f (up k)

  let size = upfunc Entl.size
  let to_string = upfunc Entl.to_string
  let print  = upfunc Entl.print
  let println = upfunc Entl.println
  let nf = upfunc Entl.nf

end
;;

module PS = struct
(* 'ee' is used for them	*)

  type t = Entl.t list

  let to_string (ee : t) =
    string_of_list Entl.to_string "\n\n" ee

  let print (ee : t) = print_string (to_string ee)

  let println (ee : t) = print_string ((to_string ee)^"\n")

  let alpha_conv (ee : t) : t = List.map Entl.alpha_conv ee
    
  let nf (ee : t) : t = List.map Entl.nf ee
    
end
;;

module SHinterval = struct
  (* 'j' is used *)
  type t = SHterm.t * SHterm.t

  let checkPresburger j =
    let (t1,t2) = j in
    T.checkPresburger t1;
    T.checkPresburger t2

  let create t0 t1 = (t0,t1)
  let left (j : t) = fst j
  let right (j : t) = snd j

  let to_string (j : t) =
    let (t0,t1) = j in
    let t0' = SHterm.to_string t0 in
    let t1' = SHterm.to_string t1 in
    "(" ^ t0' ^ "," ^ t1' ^ ")"
  let print j = print_string (to_string j)
  let println j = print_endline (to_string j)
                   
end
;;
module Invl = SHinterval
;;
module Segments = struct
  (* 'jj' is used *)
  type t = Invl.t list

  let checkPresburger jj = List.iter Invl.checkPresburger jj
         
  let to_string (jj : t) =
    let jj' = string_of_list Invl.to_string ", " jj in
    "[" ^ jj' ^ "]"
    
  let print jj = print_string (to_string jj)
               
  let println jj = print_endline (to_string jj)
                 
end
;;                
module Seg = Segments
;;


(*------------------------------*)
(* Manual Input         		*)
(*------------------------------*)
module MIfunctionIO = struct

  (* s = [(x,x@bar);(y,14);(z,a@hat+1)] *)
  type store = (string * SHterm.t) list

  (* [] is int, void, etc *)
  (* ["foo"] is struct foo *)
  (* ["foo";"ptr"] is struct foo* *)
  type mytypes = T.attr list

  (* (return-type,funcname,[(x1,types)]) *)
  type fproto = mytypes * string * (string * mytypes) list
             
  (* ret = (r,s,d,A,B) *)
  (* r:return value, s:store, d:branch, A:post, B:missing *)
  type return = T.t * store * P.t * QFSH.t * QFSH.t 
    
  type t =
    {
      mutable rawfunc : string;
      mutable func: fproto list; (* [] or [func-prototype]. This is filled after parsing rawfunc *)
      mutable s : store;
      mutable d : SHpure.t;
      mutable sh : QFSH.t;
      mutable ret : return list
    }

  let to_string_store s =
    let to_string_one (v,t) = v ^ "=" ^ (T.to_string t) in
    let body = string_of_list to_string_one ", " s in
    "[" ^ body ^ "]"

  let to_string_rawfunc f = f.rawfunc

  let to_string_return (ret : return) =
    let (r,s,d,sh1,sh2) = ret in
    let rStr = T.to_string r in
    let sStr = to_string_store s in
    let dStr = P.to_string d in
    let sh1Str = QFSH.to_string sh1 in
    let sh2Str = QFSH.to_string sh2 in
    "(" ^ rStr ^ ", " ^ sStr ^ ", " ^ dStr ^ ", " ^ sh1Str ^ ", " ^ sh2Str ^ ")"

  let to_string_returns rets =
    string_of_list to_string_return "\n" rets

  let to_string_funproto func =
    match func with
    | [] -> ""
    | (rettypes,fname,params)::_ ->
       let rettypesStr = T.to_string_attrL rettypes in
       let params1 = List.map (fun (x,attrL) -> x ^ "<" ^ (T.to_string_attrL attrL) ^ ">") params in
       let paramsStr = string_of_list (fun x -> x) ", " params1 in
       rettypesStr ^ " " ^ fname ^ " (" ^ paramsStr ^ ")"
    
  let to_string f =
    (*    let funNameBody = to_string_rawfunc f in *)
    let funNameBody = to_string_funproto f.func in
    let funNameStr = "FuncName: " ^ funNameBody ^ "\n" in
    let inputStr = "Input " ^ "\n" in
    let sStr = "s: " ^ (to_string_store f.s) ^ "\n" in
    let dStr = "d: " ^ (P.to_string f.d) ^ "\n" in
    let shStr = "A: " ^ (QFSH.to_string f.sh) ^ "\n" in
    let outputStr = "Output " ^ "\n" in
    let retStr = to_string_returns f.ret in
    funNameStr ^ inputStr ^ sStr ^ dStr ^ shStr ^ outputStr ^ retStr

  let print f = print_endline (to_string f)

  let println f = print_endline @@ (to_string f) ^ "\n"

end
;;

module MIfile = struct

  type t = MIfunctionIO.t list
         
  module FunIO = MIfunctionIO
           
  let to_string file = string_of_list FunIO.to_string "\n\n" file

  let print file = print_endline (to_string file)
                 
  let println file = print_endline ((to_string file) ^ "\n")
                 
end
;;


(*------------------------------*)
(* Some other short-cuts		*)
(*------------------------------*)
let trueSH : SH.t = ([],P.True,[]);;

(* list_bfilter [1;2;3] [t;f;t] returns [1;3] *)
let list_bfilter xx bfilter =
  let bx = List.filter (fun (b,_) -> b) (zipLst bfilter xx) in
  List.map (fun (_,y) -> y) bx
;;

(* mapFilter f [2;3;4] [t;f;t] makes [f2;f4]	*)
let mapFilter f xx bfilter =
  let xx1 = list_bfilter xx bfilter in
  List.map f xx1
;;

(* mapEqFilter x [y;z;w] [t;f;t] makes [x=y;x=w]	*)
let mapEqFilter t = mapFilter (fun x -> t =.= x);;

(* mapLtFilter x [y;z;w] [t;f;t] makes [x<y;x<w]	*)
let mapLtFilter t = mapFilter (fun x -> t <.< x);;
