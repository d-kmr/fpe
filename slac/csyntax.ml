(*-------------------------------
** Syntax for Simple C
**-------------------------------*)
open Tools
;;

(* vcpBase.Locs *)
module Locs = struct
  type t = string * int

  let dummy = ("", 0)

  let to_string (loc : t) = (string_of_int (snd loc)) ^ ":" ^ (fst loc)

  let from_cabsloc (loc : Cabs.cabsloc) =
	(loc.Cabs.filename, loc.Cabs.lineno)
    
  let to_line (_,l) = (string_of_int l)
                     
end
;;
let print_warn loc mes = Ftools.pf_s "FPAwarn" print_endline ("[W " ^ (Locs.to_string loc) ^ "] " ^ mes)
;;
let print_error loc mes = Ftools.pf_s "FPAwarn" print_endline ("[E " ^ (Locs.to_string loc) ^ "] " ^ mes)
;;
let print_mes loc mes = Ftools.pf_s "FPAwarn" print_endline ("[_ " ^ (Locs.to_string loc) ^ "] " ^ mes)
;;
let print_ex loc mes = Ftools.pf_s "FPAwarn" print_endline ("[! " ^ (Locs.to_string loc) ^ "] " ^ mes)
;;
let print_question loc mes = Ftools.pf_s "FPAwarn" print_endline ("[? " ^ (Locs.to_string loc) ^ "] " ^ mes)
;;


let rec myIndent n = if n = 0 then "" else "\t" ^ (myIndent (n-1))
;;

module Exp = struct

  type op = Add | Sub | Mul | Div | Mod | Shl | Shr | Band | Bor | Bxor
  
  type field = bytes * int option   (* (f,None) is f, (a,Some 10) is a[10] *)
             
  type tp = attr list
          
  and attr =
    | PTR
    (* Struct structname *)
    | STRUCT of bytes
    (* void F(int x) is Func(void,[(int,"x")]) *)
    | FUNC of tp * tp (* FUNC(retTp,paramTp) *)
    | FUNCPTR of tp * tp (* FUNCPTR(retTp,paramTp) *)
    | ARRAY of t list
    (* Faisal's data: "EXQ","PARAM","PTRPTR","GLOBAL","HAT","BAR","EXTERN","TILDE","CHECK","DOT","NESTED","QUESTION","DOTDOT","ACUTE","INDIRECT" *)
    | SIMPLE of int
    | OTHER of bytes
             
  and t =
    | Lval of lval
    | Int of int
    | Unknown
    | String of bytes
    | Op of op * t * t
    | Bnot of t
    | Addr of lval (* &l *)
    | Fcall of bytes * t list (* F(t..t) *)
    | Lbl of t * bytes (* t@L *)
    | Func of bytes (* F *)
    | Offset of bytes * t (* Offset(A,Arrow(Unknown,f)) is ((struct A* )0)->f for handling __builtin_offset(A,f) *)
              
  and lval =
    | Var of bytes * tp (* Var(l,[]) or Var(l,[tau]) *)
    | Arrow of t * tp * bytes (* t<tp>->f *)
    | Ptr of t (* *t *)     
    | Array of lval * t list (* a[t][u] *)

  let isVar_lval lval =
    match lval with
    | Var (_,_) -> true
    | _ -> false

  let isVar e =
    match e with
    | Lval lval -> isVar_lval lval
    | _ -> false
             
  let checkAttr a =
    match a with
    | FUNC _ -> "FUNC"
    | FUNCPTR _ -> "FUNCPTR"
    | PTR -> "PTR"
    | ARRAY _ -> "ARRAY"
    | STRUCT _ -> "STRUCT"
    | SIMPLE _ -> "SIMPLE"
    | OTHER "GLOBAL" -> "GLOBAL"
    | OTHER _ -> "OTHER"
               
  let split_tp tp =
    let ptrL = List.filter (fun a -> checkAttr a = "PTR") tp in
    let otherL = List.filter (fun a -> checkAttr a = "OTHER") tp in
    let globalL = List.filter (fun a -> checkAttr a = "GLOBAL") tp in    
    let funcL = List.filter (fun a -> checkAttr a = "FUNC" || checkAttr a = "FUNCPTR") tp in
    let arrayL = List.filter (fun a -> checkAttr a = "ARRAY") tp in
    let simpleL = List.filter (fun a -> checkAttr a = "SIMPLE") tp in
    let structL = List.filter (fun a -> checkAttr a = "STRUCT") tp in
    (ptrL,funcL,arrayL,structL,simpleL,otherL @ globalL)
    
  let extract_dim tp =
    let (ptrL,funcL,arrayL,structL,simpleL,otherL) = split_tp tp in
    let tp' = ptrL @ funcL @ structL @ simpleL @ otherL in
    match arrayL with
    | (ARRAY dim)::_ -> (tp',dim)
    | _ -> (tp,[])

  let extract_dim' tp =
    let (tp',dim') = extract_dim tp in
    let dim'' = if dim' = [] then [Int 1] else dim' in
    (tp',dim'')
         
  let hasBase tp = List.exists (fun a -> checkAttr a = "BASE") tp

  let hasFunc tp = List.exists (fun a -> checkAttr a = "FUNC" || checkAttr a = "FUNCPTR") tp

  let hasArray tp = List.exists (fun a -> checkAttr a = "ARRAY") tp

  let hasStruct tp = List.exists (fun a -> checkAttr a = "STRUCT") tp

  let hasPtr tp = List.exists (fun a -> checkAttr a = "PTR") tp

  let isFpType tp = List.exists (fun a -> checkAttr a = "FUNCPTR") tp

  let isFunType tp = List.exists (fun a -> checkAttr a = "FUNC") tp                   

  let isGlobal tp = List.exists (fun a -> checkAttr a = "GLOBAL") tp

  let isPtrType tp =
    let (ptrL,_,_,_,_,_) = split_tp tp in
    ptrL <> []

  let isBaseType tp =
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp in
    ptrL @ funcL @ arrayL @ structL = []

    (*
  let isFuncType tp = 
    let (ptrL,funcL,arrayL,structL,_) = split_tp tp in
    funcL <> [] && (ptrL @ arrayL @ structL = [])
     *)
    
  let isSimpleArrayType tp = 
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp in
    arrayL <> [] && funcL = [] && (ptrL <> [] || structL = []) 
        
  let isStructType tp =
    let (tp',dim) = extract_dim tp in
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp' in
    (dim = [] || dim = [Int (-1)]) && structL <> [] && (ptrL @ funcL = [])

  let isStructArrayType tp =
    let (tp',dim) = extract_dim tp in    
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp' in
    structL <> [] && dim <> [] && dim <> [Int (-1)] && (ptrL @ funcL = [])
    
  let isSimpleType tp = isBaseType tp || isPtrType tp
(*                     
  let isFpType tp = List.mem "FUNCPTR" (List.map checkAttr tp)

  let isFunType tp = List.mem "FUNC" (List.map checkAttr tp)
                   
  let isRealFun tp = List.mem "FUNC" (List.map checkAttr tp)
 *)
  let hasStruct tp = 
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp in
    structL <> []

  let hasArray tp = 
    let (ptrL,funcL,arrayL,structL,simpleL,_) = split_tp tp in
    arrayL <> []

  let elimArray tp =
    let (ptrL,funcL,_,structL,simpleL,otherL) = split_tp tp in
    ptrL @ funcL @ structL @ otherL

  let to_var v = Lval (Var (v,[]))

  let z = Int 0

  let rec av e =
    match e with
    | Lval l -> av_lval l
    | Int _ -> []
    | Unknown -> []
    | String _ -> []
    | Op (_,e1,e2) ->
       let vv1 = av e1 in
       let vv2 = av e2 in
       vv1 @ vv2
    | Bnot e0 -> av e0
    | Addr l -> av_lval l
    | Fcall (_,ee) -> List.flatten (List.map av ee)
    | Lbl (e0,_) -> av e0
    | Func _ -> []
    | Offset(_,e0) -> av e0
  and av_lval l =
    match l with
    | Var (v,_) -> [v]
    | Arrow (e,_,_) -> av e 
    | Ptr e -> av e 
    | Array (_,ee) -> List.flatten (List.map av ee)

  (* declared variables *)
  let rec dv l =
    match l with
    | Var (_,tp) when isFunType tp -> []
    | Var (v,_) -> []
    | Arrow (_,_,_) -> []
    | Ptr e -> av e 
    | Array (aLval,_) -> dv aLval
      
  let rec to_string_tp tp =
    let (ptrL,funcL,arrayL,structL,simpleL,otherL) = split_tp tp in
    let funcStrL = List.map to_string_attr funcL in
    let arrayStrL = List.map to_string_attr arrayL in
    let structStrL = List.map to_string_attr structL in
    let simpleStrL = List.map to_string_attr simpleL in
    let otherStrL = List.map to_string_attr otherL in
    let ptrL = List.map to_string_attr ptrL in
    let tpStrL = funcStrL @ arrayStrL @ structStrL @ simpleStrL @ otherStrL @ ptrL in
    match tpStrL with
    | [] -> "<BASE>"
    | _  -> "<" ^ (string_of_list (fun x->x) "," tpStrL) ^ ">"
  and to_string_attr attr =
    match attr with
    | STRUCT name -> "STRUCT " ^ name
    | FUNC (tpRet,tpPrm) -> "FUNC"
    | FUNCPTR (tpRet,tpPrm) -> "FUNCPTR"            
    | ARRAY ee -> "ARRAY[" ^ (string_of_list to_string "," ee) ^ "]"
    | PTR -> "PTR"
    | SIMPLE n -> "SIMPLE(" ^ (string_of_int n) ^ ")"
    | OTHER a -> a
  and to_string_field fld =
    match fld with
    | (f,None) -> f
    | (f,Some n) -> f ^ "[" ^ (string_of_int n) ^ "]"
  and to_string t =
    match t with
    | Lval l -> to_string_lval l
    | Int n -> string_of_int n
    | Unknown -> "UNKNOWN"
    | String s -> "\"" ^ (Bytes.escaped s) ^ "\""
    | Op (op,t1,t2) ->
       let t1' = to_string t1 in
       let t2' = to_string t2 in
       let op' = aux_op op in
       "(" ^ t1' ^ op' ^ t2' ^ ")"
    | Bnot t0 ->
       let t0' = to_string t0 in
       "(~" ^ t0' ^ ")"
    | Addr l ->
       let l' = to_string_lval l in
       "(&" ^ l' ^ ")"
    | Fcall (fname,tt) ->
       let tt' = string_of_list to_string "," tt in
       fname ^ "(" ^ tt' ^ ")" 
    | Lbl (t0,label) ->
       let t0' = to_string t0 in
       "(" ^ t0' ^ "@" ^ label ^ ")"
    | Func fname -> fname
    | Offset(strName,t0) -> "Offset(" ^ strName ^ "," ^ (to_string t0) ^ ")"
  and to_string_lval l =
    match l with
    | Var (v,tp) -> v ^ (to_string_tp tp)
    | Ptr t0 ->
       let t0' = to_string t0 in
       "(*" ^ t0' ^ ")"
    | Arrow (t0,tp,field) ->
       let t0' = to_string t0 in
       let tp' = if isVar t0 then "" else to_string_tp tp in
       "(" ^ t0' ^ tp' ^ "->" ^ field ^ ")"
    | Array (lval,tt) ->
       let lval' = to_string_lval lval in
       let tt' = string_of_list to_string "][" tt in
       lval' ^ "[" ^ tt' ^ "]"
  and aux_op op =
    match op with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"
    | Shl -> "<<"
    | Shr -> ">>"
    | Band -> "&"
    | Bor -> "|"
    | Bxor -> "^"

  let to_string_sub sub =
    let f (v,e) = "(" ^ v ^ "," ^ (to_string e) ^ ")" in
    "[" ^ (string_of_list f "," sub) ^ "]"
            
  let print t = print_string (to_string t)
              
  let println t = print_endline (to_string t)

  let to_string_tp tp = string_of_list to_string_attr "," tp
                
  let print_tp tp = print_string' (to_string_tp tp)

  let println_tp tp = print_endline (to_string_tp tp)
                  
  let print t = print_string (to_string t)

  let print_lval l = print_string' (to_string_lval l)
              
  let println_lval l = print_endline (to_string_lval l)
                     
  let println t = print_endline (to_string t)

  let println_sub sub = print_endline (to_string_sub sub)
                          
  let getStructName_attr a =
    match a with
    | STRUCT name -> [name]
    | _ -> []

  let getStructNameL tp = List.flatten (List.map getStructName_attr tp)
         
  let getStructName tp = List.hd (List.rev (getStructNameL tp))

  let getStructName_opt tp =
    try
      Some (getStructName tp)
    with
      _ -> None
                       
  let getArrayInfo tp =
    let _ans = ref [] in
    for i = 0 to List.length tp - 1 do
      match List.nth tp i with
      | ARRAY ee ->
         _ans := ee
      | _ -> ()
    done;
    !_ans

  let rename sub name =
    try
      match List.assoc name sub with
      | Lval (Var (v,_)) -> v
      | _ -> failwith "rename"
    with
      Not_found -> name

  let rec simple_renaming (rename: (bytes * bytes) list) e =
    match e with
    | Lval lval -> Lval (simple_renaming_lval rename lval)
    | Op (op,e1,e2) ->
       let e1' = simple_renaming rename e1 in
       let e2' = simple_renaming rename e2 in
       Op(op,e1',e2')
    | Bnot e1 ->
       let e1' = simple_renaming rename e1 in
       Bnot e1'
    | Addr lval ->
       let lval' = simple_renaming_lval rename lval in
       Addr lval'
    | Fcall (f,ee) ->
       let ee' = List.map (simple_renaming rename) ee in
       Fcall (f,ee')
    | Lbl (e1,label) ->
       let e1' = simple_renaming rename e1 in
       Lbl (e1',label)
    | Offset (strName,e1) ->
       let e1' = simple_renaming rename e1 in
       Offset (strName,e1')
    | _ -> e              
  and simple_renaming_lval rename lval =
    match lval with
    | Var (v,tp) ->
       begin
         try
           let v' = List.assoc v rename in
           let tp' = simple_renaming_tp rename tp in
           Var (v',tp')
         with
         | Not_found -> lval
       end
    | Arrow (e1,tp,fld) ->
       let e1' = simple_renaming rename e1 in
       Arrow (e1',tp,fld)
    | Ptr e1 ->
       let e1' = simple_renaming rename e1 in
       Ptr e1'
    | Array (lval,ee) ->
       let lval' = simple_renaming_lval rename lval in
       let ee' = List.map (simple_renaming rename) ee in
       Array (lval',ee')
  and simple_renaming_attr rename attr =
    match attr with
    | ARRAY ee ->
       let ee' = List.map (simple_renaming rename) ee in
       ARRAY ee'
    | _ -> attr
  and simple_renaming_tp rename tp = 
    List.map (simple_renaming_attr rename) tp

  let getFunName (e: t) =
    match e with
    | Func fname -> [fname]
    | Lval (Var (fname,tp)) when isFunType tp -> [fname]
    | _ -> []
         
  let getFunNameL (ee : t list) : bytes list =
    List.fold_left (fun ls e -> Tools.union (getFunName e) ls) [] ee
    
  let isFun t = getFunName t <> []
    
(* Subst_elim_AstAnd
def of e[p:=&l]
l1[p:=&l] -> ????
=> ( *p)[p:=&l] -> l
=> l1[p:=&l] -> l1[p:=&l]
n[p:=&e] -> n
?[p:=&e] -> ?
(e1.e2)[p:=&e] -> e1[p:=&e].e2[p:=&e]
(~e1)[p:=&e] -> ~(e1[p:=&e])
(&l)[p:=&e] -> &(l[p:=&e])
F(e1,e2)[p:=&e] -> F(e1[p:=&e],e2[p:=&e])
(e1@L)[p:=&e] -> (e1[p:=&e]@L)

def of l[p:=&]
x[p:=&e] -> x
(e1->f)[p:=&e] -> (e1[p:=&e])->f
( *e1)[p:=&e] -> *(e1[p:=&e])
(a[e1])[p:=&e] -> a[e1[p:=&e]]
 *)
  let cast_support v tp_before tp_after =
    let (ptrL,funcL,arrayL,structL,simpleL,otherL) = split_tp tp_before in
    let (_,_,_,structL_after,_,_) = split_tp tp_after in
    match structL,structL_after with
    | [STRUCT str_before],[STRUCT str_after] ->
       let tp_new = ptrL @ funcL @ arrayL @ [STRUCT str_after] @ simpleL @ otherL in
       let v_bf = Var (v,tp_before) in
       let v_nw = Var (v,tp_new) in
       Ftools.pf_s "FPAdebug" print_endline ("CAST support: " ^ (to_string_lval v_bf) ^ " --> " ^ (to_string_lval v_nw));
       tp_new
    | _,_ -> tp_before
    
  let rec subst_elim_AstAnd sub e =
    match e with
    | Lval (Var (v,tp)) ->
       begin
         try
           match List.assoc v sub with
           | Lval (Var(v',tp')) ->
              let tp1 = cast_support v' tp' tp in
              Lval (Var(v',tp1))
           | e -> e
         with
           Not_found -> e
       end
    | Lval l ->
       let l' = subst_elim_AstAnd_lval sub l in
       Lval l'
    | Int _ -> e
    | Unknown -> e
    | String _ -> e
    | Op (op,e1,e2) ->
       let e1' = subst_elim_AstAnd sub e1 in
       let e2' = subst_elim_AstAnd sub e2 in
       Op (op,e1',e2')
    | Bnot e0 ->
       let e0' = subst_elim_AstAnd sub e0 in
       Bnot e0'
    | Addr l ->
       let l' = subst_elim_AstAnd_lval sub l in
       Addr l'
    | Fcall (fname,ee) ->
       let ee' = List.map (subst_elim_AstAnd sub) ee in
       let fname_split = cut_string '!' fname in (* fname has the form myfunc!4 *)
       let fname1 = List.nth fname_split 0 in
       let pos = List.nth fname_split 1 in
       let fname2 =
         try
           match List.assoc fname1 sub with
           | Lval (Var (f,_)) -> f
           | _ -> raise Not_found
         with
           Not_found -> fname1
       in
       let fname' = fname2 ^ "!" ^ pos in
       Fcall (fname',ee')
    | Lbl (e0,label) ->
       let e0' = subst_elim_AstAnd sub e0 in
       Lbl (e0',label)
    | Func _ -> e
    | Offset (strName,e0) ->
       let e0' = subst_elim_AstAnd sub e0 in
       Offset (strName,e0')
  and subst_elim_AstAnd_lval sub l =
    match l with
    | Var (v,tp) ->
       begin
         try
           match List.assoc v sub with
           | Lval l' -> l'
           | _ -> raise Not_found
         with
           Not_found -> l
       end
    | Arrow (e,tp,field) ->
       let e' = subst_elim_AstAnd sub e in
       Arrow (e',tp,field)
    | Ptr (Lval (Var (v,tp))) ->
       begin
         try
           match List.assoc v sub with
           | Addr l' -> l'
           | e' -> Ptr e'
         with
           Not_found -> l
       end
    | Ptr e ->
       let e' = subst_elim_AstAnd sub e in
       Ptr e'
    | Array (aLval,ee) ->
       let aLval' = subst_elim_AstAnd_lval sub aLval in
       let ee' = List.map (subst_elim_AstAnd sub) ee in
       Array (aLval',ee')
    
  (* This is called from Stmt.transform_exp *)
  let rec f_exp_elim_astand e =
    match e with
    | Lval lval ->
       let lval' = f_lval_elim_astand lval in
       Lval lval'
    | Int n -> Int n
    | Unknown -> Unknown
    | String s -> String s
    | Op (op,e1,e2) ->
       let e1' = f_exp_elim_astand e1 in
       let e2' = f_exp_elim_astand e2 in
       Op (op,e1',e2')
    | Bnot e0 ->
       let e0' = f_exp_elim_astand e0 in
       Bnot e0'
    | Addr lval ->
       let lval' = f_lval_elim_astand lval in
       Addr lval'
    | Fcall (fname,ee) ->
       let ee' = List.map f_exp_elim_astand ee in
       Fcall (fname,ee')
    | Lbl (e0,label) ->
       let e0' = f_exp_elim_astand e0 in
       Lbl (e0',label)
    | Func fname -> Func fname
    | Offset (strName,e0) ->
       let e0' = f_exp_elim_astand e0 in
       Offset (strName,e0')
  and f_lval_elim_astand l =
    match l with
    | Var (v,tpL) -> Var (v,tpL)
    | Arrow (e,tp,fld) ->
       let e' = f_exp_elim_astand e in
       Arrow (e',tp,fld)
    | Ptr (Addr lval) -> f_lval_elim_astand lval
    | Ptr e ->
       let e' = f_exp_elim_astand e in
       Ptr e'
    | Array (aLval,ee) ->
       let ee' = List.map f_exp_elim_astand ee in
       Array (aLval,ee')

  let rec getTrueType_opt strV aliases e =
    match e with
    | Lval lval -> getTrueType_lval_opt strV aliases lval
    | Op (_,e1,_) -> getTrueType_opt strV aliases e1
    | Int n -> Some []
    | String s -> Some []
    | Bnot _ -> Some []
    | Addr lval ->
       begin
         match getTrueType_lval_opt strV aliases lval with
         | None -> None
         | Some tp -> Some (PTR :: tp)
       end
    | _ -> None
  and getTrueType_lval_opt strV aliases lval =
    match lval with
    | Var (_,tp) -> Some tp
    | Arrow (e1,tp,fld) ->
       begin
         match getStructName_opt tp with
         | None -> None
         | Some strName ->
            let strName1 = getRealStrName aliases strName in
            match V.find_opt strName1 strV with
            | None -> None
            | Some (_,fldTpL) -> List.assoc_opt fld fldTpL
       end
    | Ptr e1 -> 
       begin
         match getTrueType_opt strV aliases e1 with
         | None -> None
         | Some tp ->
            let (ptrL,funcL,arrayL,structL,simpleL,otherL) = split_tp tp in
            if ptrL = [] then Some tp
            else
              Some ((List.tl ptrL)@funcL@arrayL@structL@simpleL@otherL)
       end
    | Array (lval,_) -> getTrueType_lval_opt strV aliases lval
  and getRealStrName aliases strName =
    let rec aux prev cur =
      match V.find_opt cur aliases with
      | None -> cur
      | Some next when next = cur -> cur
      | Some next -> aux cur next
    in
    aux "" strName

  let hasFunPtrTp strV aliases e =
    match getTrueType_opt strV aliases e with
    | Some tp when isFpType tp -> true
    | _ -> false

  let getFpName_lval lval =
    match lval with
    | Ptr (Lval (Var (fp,tp))) when isFpType tp -> [fp]
    | Var (fp,tp) when isFpType tp -> [fp]
    | _ -> []

  let getFpName t =
    match t with
    | Lval lv -> getFpName_lval lv
    | _ -> []

  let getFpNameL ee =
    List.fold_left (fun ls e -> Tools.union (getFpName e) ls) [] ee
         
  let getFunctionTp tp =
    let (_,funcL,_,_,_,_) = split_tp tp in
    let _tpRet = ref [] in
    let _tpPrm = ref [] in
    for i = 0 to List.length funcL - 1 do
      match List.nth funcL i with
      | FUNC (tpRet,tpPrm) ->
         _tpRet := tpRet @ !_tpRet;
         _tpPrm := tpPrm @ !_tpPrm
      | FUNCPTR (tpRet,tpPrm) ->
         _tpRet := tpRet @ !_tpRet;
         _tpPrm := tpPrm @ !_tpPrm
      | _ -> ()
    done;
    (!_tpRet,!_tpPrm)
         
  let isFp_lval lval = getFpName_lval lval <> []
         
  let isFp t = getFpName t <> []

  let rec getTp t =
    match t with
    | Lval lval -> getTp_lval lval
    | Func _ -> [] (* DUMMY. Unused *)
    | _ -> []
  and getTp_lval lval = 
    match lval with
    | Var (_,tp) -> tp
    | Arrow (e,tp,fld) -> [] (* DUMMY *)
    | Array (_,ee) -> [ARRAY ee]
    | _ -> []

  let getVarName_lval lval = 
    match lval with
    | Var (v,_) -> v
    | Arrow (e,_,_) -> to_string e (* DUMMY *)
    | _ -> "" (* DUMMY *)

  let getVarName t = 
    match t with
    | Lval lval -> getVarName_lval lval
    | Func f -> f                 
    | Int _ -> "<num>" (* DUMMY *)
    | Unknown -> "<unknown>" (* DUMMY *)
    | String s -> s (* DUMMY *)
    | Op _ -> "<op>" (* DUMMY *)
    | Bnot _ -> "<bnot>" (* DUMMY *)
    | Addr _ -> "<addr>" (* DUMMY *)
    | Fcall _ -> "<fcall>" (* DUMMY *)
    | Lbl _ -> "<label>"  (* DUMMY *)
    | Offset _ -> "<offset>" (* DUMMY *)
    
  let getNum t =
    match t with
    | Int n -> n
    | _ -> 0 (* DUMMY *)
             
  let rec isEvaluatable t =
    match t with
    | Lval lval -> isEvaluatable_lval lval
    | Int _ -> true
    | Unknown -> false
    | String _ -> false
    | Op (_,t1,t2) -> (isEvaluatable t1) && (isEvaluatable t2)
    | Bnot t1 -> (isEvaluatable t1)
    | Addr lval -> isEvaluatable_lval lval
    | Fcall (_,_) -> false
    | Lbl (t0,_) -> isEvaluatable t0
    | Func _ -> false
    | Offset _ -> false
  and isEvaluatable_lval lval =
    match lval with
    | Var (_,tp) -> ((not (hasFunc tp)) && (not (hasStruct tp)) || (hasPtr tp))
    | Arrow _ -> false
    | Ptr t0 -> isEvaluatable t0
    | Array (lval,tt) -> (isEvaluatable_lval lval) && (List.for_all isEvaluatable tt)

  let rec isRetVal e =
    match e with
    | Lval lval -> isRetVal_lval lval
    | _ -> false
  and isRetVal_lval lval =
    match lval with
    | Var (v,_) -> v = "$ret"
    | _ -> false

  let getFpHolderName aliases e =
    match e with
    | Lval (Var (v,tp)) when isGlobal tp && isFpType tp -> v
    | Lval (Arrow (_,tp,fld) ) ->
       let strName = getStructName tp in
       let strName1 = getRealStrName aliases strName in
       strName1 ^ "->" ^ fld
    | _ -> "NotFpHolder"

  let getFpHolder strV aliases e =
    match getTrueType_opt strV aliases e with
    | Some tp when isFpType tp ->
       begin
         match e with
         | Lval (Var (v,tp')) when isGlobal tp' ->
            [e]
         | Lval (Arrow (_,_,_) ) -> [e]
         | _ -> []
       end
    | _ -> []

  let getFpHolderL strV aliases ee =
    List.fold_left (fun ls e -> Tools.union (getFpHolder strV aliases e) ls) [] ee

  let getFpHolder_lval strV aliases (lval: lval) : lval list =
    match getTrueType_opt strV aliases (Lval lval) with
    | Some tp when isFpType tp ->
       begin
         match lval with
         | Var (v,tp) when isGlobal tp -> [Var (v,tp)]
         | Arrow (a,b,c) -> [Arrow (a,b,c)]
         | _ -> []
       end
    | _ -> []          

  (* This is used for function parameters *)
  let isFpFun t = (isFun t) || (isFp t)
         
end
;;

module Bexp = struct

  type t =
    | Eq of Exp.t * Exp.t
    | Neq of Exp.t * Exp.t
    | Lt of Exp.t * Exp.t
    | Le of Exp.t * Exp.t
    | And of t * t
    | Or of t * t
    | Not of t 
    | Lbl of t * bytes (* b@L *)

  let true_ = Eq (Exp.z,Exp.z)
           
  let false_ = Neq (Exp.z,Exp.z)
           
  let rec av b =
    match b with
    | Eq (e1,e2) ->
       let vv1 = Exp.av e1 in
       let vv2 = Exp.av e2 in
       vv1 @ vv2
    | Neq (e1,e2) ->
       let vv1 = Exp.av e1 in
       let vv2 = Exp.av e2 in
       vv1 @ vv2
    | Lt (e1,e2) ->
       let vv1 = Exp.av e1 in
       let vv2 = Exp.av e2 in
       vv1 @ vv2
    | Le (e1,e2) ->
       let vv1 = Exp.av e1 in
       let vv2 = Exp.av e2 in
       vv1 @ vv2
    | And (b1,b2) ->
       let vv1 = av b1 in
       let vv2 = av b2 in
       vv1 @ vv2
    | Or (b1,b2) ->
       let vv1 = av b1 in
       let vv2 = av b2 in
       vv1 @ vv2
    | Not b0 -> av b0
    | Lbl (b0,_) -> av b0
           
  let to_string b =
    let rec aux b =
      match b with
      | Eq (e1,e2) ->
         let e1' = Exp.to_string e1 in
         let e2' = Exp.to_string e2 in
         "(" ^ e1' ^ " == " ^ e2' ^ ")"
      | Neq (e1,e2) ->
         let e1' = Exp.to_string e1 in
         let e2' = Exp.to_string e2 in
         "(" ^ e1' ^ " != " ^ e2' ^ ")"
      | Lt (e1,e2) ->
         let e1' = Exp.to_string e1 in
         let e2' = Exp.to_string e2 in
         "(" ^ e1' ^ " < " ^ e2' ^ ")"
      | Le (e1,e2) -> 
         let e1' = Exp.to_string e1 in
         let e2' = Exp.to_string e2 in
         "(" ^ e1' ^ " <= " ^ e2' ^ ")"
      | And (b1,b2) ->
         let b1' = aux b1 in
         let b2' = aux b2 in
         "(" ^ b1' ^ " && " ^ b2' ^ ")"
      | Or (b1,b2) ->
         let b1' = aux b1 in
         let b2' = aux b2 in
         "(" ^ b1' ^ " || " ^ b2' ^ ")"
      | Not t ->
         let b' = aux t in
         "(!" ^ b' ^ ")"
      | Lbl (t,label) ->
         let t' = aux t in
         t' ^ "@" ^ label
    in
    aux b

  let print b = print_string (to_string b)
              
  let println b = print_endline (to_string b)    

  (* Substitution *)
  let rec subst_elim_AstAnd sub b =
    match b with
    | Eq (e1,e2) ->
       let e1' = Exp.subst_elim_AstAnd sub e1 in
       let e2' = Exp.subst_elim_AstAnd sub e2 in
       Eq (e1',e2')
    | Neq (e1,e2) ->
       let e1' = Exp.subst_elim_AstAnd sub e1 in
       let e2' = Exp.subst_elim_AstAnd sub e2 in
       Neq (e1',e2')
    | Lt (e1,e2) ->
       let e1' = Exp.subst_elim_AstAnd sub e1 in
       let e2' = Exp.subst_elim_AstAnd sub e2 in
       Lt (e1',e2')
    | Le (e1,e2) ->
       let e1' = Exp.subst_elim_AstAnd sub e1 in
       let e2' = Exp.subst_elim_AstAnd sub e2 in
       Le (e1',e2')
    | And (b1,b2) ->
       let b1' = subst_elim_AstAnd sub b1 in
       let b2' = subst_elim_AstAnd sub b2 in
       And (b1',b2')
    | Or (b1,b2) ->
       let b1' = subst_elim_AstAnd sub b1 in
       let b2' = subst_elim_AstAnd sub b2 in
       Or (b1',b2')
    | Not b0 ->
       let b0' = subst_elim_AstAnd sub b0 in
       Not b0'
    | Lbl (b0,label) ->
       let b0' = subst_elim_AstAnd sub b0 in
       Lbl (b0',label)
                
  (* normal form = negation-free form *)
  (* obtained by de Morgan + transformation of atomic formulas *)
  let rec nf b =
    match b with
    | Eq _ -> b
    | Neq _ -> b
    | Lt _ -> b
    | Le _ -> b
    | And (b1,b2) ->
       let b1' = nf b1 in
       let b2' = nf b2 in
       And (b1',b2')
    | Or (b1,b2) ->
       let b1' = nf b1 in
       let b2' = nf b2 in
       Or (b1',b2')
    | Not b1 -> nf_neg b1
    | Lbl (b1,lbl) ->
       let b1' = nf b1 in
       Lbl (b1',lbl)
  and nf_neg b =
    match b with
    | Eq (t1,t2) -> Neq (t1,t2)
    | Neq (t1,t2) -> Eq (t1,t2)
    | Lt (t1,t2) -> Le (t2,t1)
    | Le (t1,t2) -> Lt (t2,t1)
    | And (b1,b2) ->
       let b1' = nf_neg b1 in
       let b2' = nf_neg b2 in
       Or (b1',b2')
    | Or (b1,b2) ->
       let b1' = nf_neg b1 in
       let b2' = nf_neg b2 in
       And (b1',b2')
    | Not b1 -> nf b1
    | Lbl (b1,lbl) ->
       let b1' = nf_neg b1 in
       Lbl (b1',lbl)

  (* This is a part of Stmt.transform_exp *)
  let transform_exp ff b = 
    let (f_lval,f_exp) = ff in
    let rec aux b0 =
      match b0 with
      | Eq (t1,t2) ->
         let t1' = f_exp t1 in
         let t2' = f_exp t2 in
         Eq (t1',t2')
      | Neq (t1,t2) ->
         let t1' = f_exp t1 in
         let t2' = f_exp t2 in
         Neq (t1',t2')
      | Lt (t1,t2) ->
         let t1' = f_exp t1 in
         let t2' = f_exp t2 in
         Lt (t1',t2')
      | Le (t1,t2) ->
         let t1' = f_exp t1 in
         let t2' = f_exp t2 in
         Le (t1',t2')
      | And (b1,b2) ->
         let b1' = aux b1 in
         let b2' = aux b2 in
         And (b1',b2')
      | Or (b1,b2) ->
         let b1' = aux b1 in
         let b2' = aux b2 in
         Or (b1',b2')
      | Not b1 -> 
         let b1' = aux b1 in
         Not b1'
    | Lbl (b1,lbl) ->
       let b1' = aux b1 in
       Lbl (b1',lbl)
    in
    aux b


  let rec simple_renaming rename bexp =
    match bexp with
    | Eq (t1,t2) ->
       let t1' = Exp.simple_renaming rename t1 in
       let t2' = Exp.simple_renaming rename t2 in
       Eq (t1',t2')
    | Neq (t1,t2) ->
       let t1' = Exp.simple_renaming rename t1 in
       let t2' = Exp.simple_renaming rename t2 in
       Neq (t1',t2')
    | Lt (t1,t2) ->
       let t1' = Exp.simple_renaming rename t1 in
       let t2' = Exp.simple_renaming rename t2 in
       Lt (t1',t2')
    | Le (t1,t2) ->
       let t1' = Exp.simple_renaming rename t1 in
       let t2' = Exp.simple_renaming rename t2 in
       Le (t1',t2')
    | And (b1,b2) ->
       let b1' = simple_renaming rename b1 in
       let b2' = simple_renaming rename b2 in
       And (b1',b2')
    | Or (b1,b2) ->
       let b1' = simple_renaming rename b1 in
       let b2' = simple_renaming rename b2 in
       Or(b1',b2')
    | Not b1 ->
       let b1' = simple_renaming rename b1 in
       Not b1'
    | Lbl (b1,lbl) ->
       let b1' = simple_renaming rename b1 in
       Lbl (b1',lbl)
    
end
;;

module Init = struct
  (* initializing expression *)
  (* E --> no initializer *)
  (* S 3 --> 3 (initializer for simple type) *)
  (* M [S 3;S 5] --> {3,5} (initializer for struct/array) *)
  (* M [] --> {} (initializer for non-initialized array) *)
  type t = None | S of Exp.t | M of t list

  let isSingleInit loc init =
    match init with
    | S _ -> true      
    | _ -> false
    
  (* { e1, e2 } -> { F(e1), F(e2) } *)
  let rec map (f: Exp.t -> Exp.t) init =
    match init with
    | None -> None
    | S e -> S (f e)
    | M initL -> M (List.map (map f) initL)
       
  let rec to_string init = 
    match init with
    | None -> "None"
    | S e -> Exp.to_string e
    | M initL ->
       let initL' = string_of_list to_string "," initL in
       "{" ^ initL' ^ "}"       

  let println init = print_endline (to_string init)

  let rec simple_renaming rename init =
    match init with
    | None -> None
    | S e ->
       let e' = Exp.simple_renaming rename e in
       S e'
    | M initL ->
       let initL' = List.map (simple_renaming rename) initL in
       M initL'
       
end
;;

module Decl = struct

(* 
    int x;  --> (Int,x, Init [])
    int a[3]; --> (Int, a[3], Init [])
    void f(); --> (Func(void,[]), f, Init [])
    void ( *f)(int x); --> (Ptr(Func(void,[(int,x)])), f, Init [])
    int x=3; --> (Int, x, InitAtom ("",3))
    struct A st = { x:1 }; --> (Struct A, st, Init [(x,1)]) 
*)

  type t = Decl of Exp.tp * Exp.lval * Init.t

  let getTp d =
    let Decl (tp,_,_) = d in
    tp
                 
  let av d =
    let Decl (_,lval,_) = d in
    Exp.av_lval lval

  let dv d =
    let Decl (_,lval,_) = d in
    Exp.dv lval
    
  (* int ( *x) --> (int* ) x *)
  let rec shift_ptr_left decl =
    let Decl (tp,lval,init) = decl in
    match lval with
    | Exp.Ptr (Exp.Lval lval1)  ->
       let decl' = Decl (Exp.PTR :: tp,lval1,init) in
       shift_ptr_left decl'
    | _ -> decl
         
  (* (int* )  x) --> int ( *x) *)
  let shift_ptr_right decl =
    let Decl (tp,lval,init) = decl in
    let (ptrL,funcL,arrayL,structL,simpleL,otherL) = Exp.split_tp tp in
    let tp_nptr = funcL @ arrayL @ structL @ simpleL @ otherL in
    let rec aux l pL =
      match pL with
      | [] -> l
      | p::pL' -> aux (Exp.Ptr (Exp.Lval lval)) pL'
    in
    let lval' = aux lval ptrL in
    Decl (tp_nptr, lval',init)
    
  let to_string0 decl =
    let Decl (tp,l,init) = decl in
    let head = Exp.to_string_lval l in
    match init with
    | Init.None -> head
    | _ -> head ^ " = " ^ (Init.to_string init)
      
  let to_string indent decl =
    (myIndent indent) ^ (to_string0 decl) ^ "; "
       
  let print d = print_string (to_string 0 d)
              
  let println d = print_endline (to_string 0 d)

  let println' header d = print_endline (header ^ (to_string  0 d))
                
  (* Substitution *)
  let subst_elim_AstAnd vv sub d =
    let Decl (tp,lval,init) = d in
    match Exp.isFpType tp, Exp.isFunType (Exp.getTp_lval lval) with
    | true,_ -> (vv,sub,d)
    | _,true -> (vv,sub,d)
    | _,_ -> 
       let dv = Exp.dv lval in
       match intersect dv vv with
       | [] -> (vv,sub,d)
       | vv' ->
          let vvFresh = genFreshVarL "$_" vv (List.length vv') in
          let eeFresh = List.map Exp.to_var vvFresh in
          let subFresh = zipLst vv' eeFresh in
          let sub1 = subFresh @ sub in
          let vv1 = vv @ vvFresh in
          let lval' = Exp.subst_elim_AstAnd_lval sub1 lval in
          let init' = Init.map (Exp.subst_elim_AstAnd sub1) init in
          let d1 = Decl (tp,lval',init') in
          (vv1,sub1,d1)

  let transform_exp ff d =
    let (f_lval,f_exp) = ff in
    let Decl (tp,lval,init) = d in
    let lval' = f_lval lval in
    let init' = Init.map f_exp init in    
    Decl (tp,lval',init')

  let simple_renaming rename decl =
    let Decl (tp,lval,init) = decl in
    let tp' = Exp.simple_renaming_tp rename tp in
    let lval' = Exp.simple_renaming_lval rename lval in
    let init' = Init.simple_renaming rename init in
    Decl (tp',lval',init')
    
end
;;

module Stmt = struct

  type t =
    | Skip
    | Decl of Decl.t * Locs.t
    | Asgn of Exp.lval * Exp.t * Locs.t  (* l = t; *)
    | Malloc of bytes * Exp.tp * Exp.t * Locs.t (* x = malloc(sizeof(t)*u; *)
    | Free of Exp.t  * Locs.t (* free(t); *)
    | Block of t list  * Locs.t (* { P1;P2;P3 } *)
    | If of Bexp.t * t * t  * Locs.t (* if(b) P1 else P2; *)
    | While of Bexp.t * Bexp.t list * t  * Locs.t (* while(b & bb_extra) P; *)
    | Fcall of bytes * Exp.t list * Exp.tp * Exp.tp * Locs.t (* (F,prmL,tpRetL,tpPrmL,loc) -> F(t1,..,tn) *)
    | FPcall of bytes * int * Exp.t list * Exp.tp * Exp.tp * Locs.t (* (fp,pos,prmL,tpRetL,tpPrmL,loc) -> fp!pos(t..t) *)
    | Return of Exp.t  * Locs.t (* return(t); *)
    | Lbl of bytes  * bytes list * Locs.t (* L:: *)
    (* Note: Lbl(L,[x;y],loc) means that x@L and y@L will appear later *)
    | Continue of Locs.t
    | Break of Locs.t
    | Fail of Locs.t
    | Unknown of Locs.t
               
  let to_string prompt indent p =
    let rec aux idt p =
      let myIndent = prompt ^ (myIndent idt) in
      match p with
      | Skip -> myIndent ^ "skip; "
      | Decl (decl,loc) -> prompt ^ (Decl.to_string indent decl)
      | Asgn (l,t,loc) ->
         let l' = Exp.to_string_lval l in
         let t' = Exp.to_string t in         
         myIndent ^ l' ^ "=" ^ t' ^ "; "
      | Malloc (v,tp,u,loc) ->
         let tp' = Exp.to_string_tp tp in
         let u' = Exp.to_string u in
         myIndent ^ v ^ "=malloc(sizeof(" ^ tp' ^ ")*" ^ u' ^ "); "
      | Free (t,loc) ->
         let t' = Exp.to_string t in
         myIndent ^ "free(" ^ t' ^ "); "
      | Block (pp,loc) -> "{" ^ string_of_list (aux idt) "\n" pp ^ "}"
      | If (b,p1,p2,loc) ->
         let p1' = aux (idt+1) p1 in
         let p2' = aux (idt+1) p2 in
         let b' = Bexp.to_string b in
         myIndent ^ "if " ^ b' ^ "\n" ^ p1' ^ "\n" ^ myIndent ^ "else\n" ^ p2'
      | While (b,bb,p,loc) ->
         let p' = aux (idt+1) p in
         let bb1 = b::bb in
         let bb' = List.fold_left
                     (fun l->fun x-> if x = "TRUE" then l else (l ^ " & " ^ x))
                     "TRUE"
                     (List.map Bexp.to_string bb1)
         in
         myIndent ^ "while " ^ bb' ^ "\n" ^ p'
      | Fcall (fname,tt,retTp,prmTp,loc) ->
         let tt' = string_of_list Exp.to_string "," tt in
         myIndent ^ fname ^ "(" ^ tt' ^ ");"
      | FPcall (fp,pos,tt,retTp,prmTp,loc) ->
         let tt' = string_of_list Exp.to_string "," tt in
         let pos' = string_of_int pos in
         myIndent ^ fp ^ "!" ^ pos' ^ "(" ^ tt' ^ ");"
      | Return (t,loc) ->
         let t' = Exp.to_string t in
         myIndent ^ "return " ^ t' ^ "; "
      | Lbl (label,varL,loc) ->
         myIndent ^ label ^ ":: <" ^ (string_of_list (fun x->x) "," varL) ^ ">"
      | Break loc -> myIndent ^ "break; "
      | Continue loc -> myIndent ^ "continue; "
      | Fail loc -> myIndent ^ "FAIL; " 
      | Unknown loc -> myIndent ^ "UNKNOWN; "
    in
    aux indent p

  let print e = print_string (to_string "" 0 e)
              
  let println e = print_endline (to_string "" 0 e)    

  let println' header e = print_endline (to_string header 0 e)

  let c = ref 0

  let rec isSkip stmt =
    match stmt with
    | Skip -> true
    | Block (stmtL,_) -> List.for_all isSkip stmtL
    | _ -> false
                        
  let unBlock stmt =
    match stmt with
    | Block (stmtL,loc) -> stmtL
    | _ -> [stmt]

  let mkBlock stmtL loc = Block (stmtL,loc)

  (* apply f (of type stmt->stmt) recursively to the input statement *)
  let rec apply f stmt =
    match stmt with
    | Block (stmtL,loc) -> mkBlock (List.map (apply f) stmtL) loc
    | If (cond,sThen,sElse,loc) ->
       let sThen1 = apply f sThen in
       let sElse1 = apply f sElse in
       If (cond,sThen1,sElse1,loc)
    | While (cond,condex,sBody,loc) ->
       let sBody1 = apply f sBody in
       While (cond,condex,sBody1,loc)
    | _ -> f stmt
                    
  (* all variables *)
  let rec av stmt =
    match stmt with
    | Skip -> []
    | Decl (decl,_) -> Decl.av decl
    | Asgn (l,e,_) ->
       let vv_l = Exp.av_lval l in
       let vv_e = Exp.av e in
       union vv_l vv_e
    | Malloc (v,_,u,_) ->
       let vv_u = Exp.av u in
       union [v] vv_u
    | Free (e,_) -> Exp.av e
    | Block (stmtL,_) -> unionL (List.map av stmtL)
    | If (b,stmtThen,stmtElse,_) ->
       let vv_b = Bexp.av b in
       let vv1 = av stmtThen in
       let vv2 = av stmtElse in
       unionL [vv_b; vv1; vv2]
    | While (b,bb,stmtBody,_) ->
       let vv_b = List.flatten (List.map Bexp.av (b::bb)) in
       let vv_body = av stmtBody in
       union vv_b vv_body
    | Fcall (_,ee,_,_,_) -> unionL (List.map Exp.av ee)
    | FPcall (_,_,ee,_,_,_) -> unionL (List.map Exp.av ee)
    | Return (e,_) -> Exp.av e
    | Lbl (_,_,_) -> []
    | Break _ -> []
    | Continue _ -> []             
    | Fail _ -> []
    | Unknown _ -> []
                 
  (* declared variables *)
  let rec dv stmt =
    match stmt with
    | Decl (decl,_) -> Decl.dv decl
    | Block (stmtL,_) -> unionL (List.map dv stmtL)
    | If (b,stmtThen,stmtElse,_) -> union (dv stmtThen) (dv stmtElse)
    | While (b,bb,stmtBody,_) -> dv stmtBody
    | _ -> []
                 
  let getloc stmt =
    match stmt with
    | Skip -> Locs.dummy
    | Decl (_,loc)
      | Asgn (_,_,loc)
      | Malloc (_,_,_,loc)
      | Free (_,loc)
      | Block (_,loc)
      | If (_,_,_,loc)
      | While (_,_,_,loc)
      | Fcall (_,_,_,_,loc)
      | FPcall (_,_,_,_,_,loc)
      | Return (_,loc)
      | Lbl (_,_,loc)
      | Break loc
      | Continue loc
      | Fail loc
      | Unknown loc -> loc
                 
  let rec extractFP stmt =
    match stmt with
    (* #f = fp case *)
    | Asgn (lval,e,loc) when Exp.isVar_lval lval && Exp.isFp e ->
       let fp = List.hd (Exp.getFpName e) in
       let fvar = Exp.getVarName_lval lval in
       [(fvar,fp)]
    | Block (stmtL,loc) -> List.flatten (List.map extractFP stmtL)
    | If (_,stmtThen,stmtElse,loc) -> (extractFP stmtThen) @ (extractFP stmtElse)
    | While (_,_,stmtBody,loc) -> extractFP stmtBody
    | _ -> []

  let rec simple_renaming rename stmt =
    match stmt with
    | Decl (decl,loc) ->
       let decl' = Decl.simple_renaming rename decl in
       Decl (decl',loc)
    | Asgn (lval,e,loc) ->
       let lval' = Exp.simple_renaming_lval rename lval in
       let e' = Exp.simple_renaming rename e in
       Asgn (lval',e',loc)
    | Malloc (x,tp,e,loc) ->
       let x' = try List.assoc x rename with _ -> x in
       let tp' = Exp.simple_renaming_tp rename tp in
       let e' = Exp.simple_renaming rename e in
       Malloc (x',tp',e',loc)
    | Free (e,loc) ->
       let e' = Exp.simple_renaming rename e in
       Free (e',loc)
    | If (b,stmtThen,stmtElse,loc) ->
       let b' = Bexp.simple_renaming rename b in
       let stmtThen' = simple_renaming rename stmtThen in
       let stmtElse' = simple_renaming rename stmtElse in
       If (b',stmtThen',stmtElse',loc)
    | While (b,bb,stmtBody,loc) ->
       let b' = Bexp.simple_renaming rename b in
       let bb' = List.map (Bexp.simple_renaming rename) bb in
       let stmtBody' = simple_renaming rename stmtBody in
       While (b',bb',stmtBody',loc)
    | Fcall (fname,ee,tpRet,tpPrm,loc) ->
       let fname' = try List.assoc fname rename with _ -> fname in       
       let ee' = List.map (Exp.simple_renaming rename) ee in
       Fcall (fname',ee',tpRet,tpPrm,loc)
    | FPcall (fp,pos,ee,tpRet,tpPrm,loc) ->
       let fp' = try List.assoc fp rename with _ -> fp in
       let ee' = List.map (Exp.simple_renaming rename) ee in
       FPcall (fp',pos,ee',tpRet,tpPrm,loc)
    | Return (e,loc) ->
       let e' = Exp.simple_renaming rename e in
       Return (e',loc)
    | Block (stmtL,loc) ->
       let stmtL' = List.map (simple_renaming rename) stmtL in
       Block (stmtL',loc)
    | _ -> stmt
         
  (* substitution *)                  
  let rec subst_elim_AstAnd vv sub stmt =
    let _vvOut = ref vv in
    let _subOut = ref sub in
    let _stmtOut = ref [stmt] in
    begin
      match stmt with
      | Skip -> ()
      | Decl (decl,loc) ->
         let (vv',sub',decl') = Decl.subst_elim_AstAnd vv sub decl in
         let stmt' = Decl (decl',loc) in
         _vvOut := vv';
         _subOut := sub';
         _stmtOut := [stmt']
      | Asgn (lval,e,loc) ->
         let lval' = Exp.subst_elim_AstAnd_lval sub lval in
         let e' = Exp.subst_elim_AstAnd sub e in
         let stmt' = Asgn (lval',e',loc) in
         _stmtOut := [stmt']
      | Malloc (x,tp,e,loc) ->
         let x' = Exp.rename sub x in
         let e' = Exp.subst_elim_AstAnd sub e in
         let stmt' = Malloc (x',tp,e',loc) in
         _stmtOut := [stmt']
      | Free (e,loc) ->
         let e' = Exp.subst_elim_AstAnd sub e in
         let stmt' = Free (e',loc) in
         _stmtOut := [stmt']
      | If (b,stmtThen,stmtElse,loc) ->
         let b' = Bexp.subst_elim_AstAnd sub b in
         let (vv1,sub1,stmtThen') = subst_elim_AstAnd vv sub stmtThen in
         let (vv2,sub2,stmtElse') = subst_elim_AstAnd vv1 sub1 stmtElse in
         let stmt' = If (b',stmtThen',stmtElse',loc) in
         _vvOut := vv2;
         _subOut := sub2;
         _stmtOut := [stmt']
      | While (b,bb,stmtBody,loc) ->
         let b' = Bexp.subst_elim_AstAnd sub b in
         let bb' = List.map (Bexp.subst_elim_AstAnd sub) bb in
         let (vv',sub',stmtBody') = subst_elim_AstAnd vv sub stmtBody in
         let stmt' = While (b',bb',stmtBody',loc) in
         _vvOut := vv';
         _subOut := sub';
         _stmtOut := [stmt']
      | Fcall (fname,ee,tpRet,tpPrm,loc) ->
         let ee' = List.map (Exp.subst_elim_AstAnd sub) ee in
         let fname' =
           try
             match List.assoc fname sub with
             | Exp.Lval (Exp.Var (f,_)) -> f
             | _ -> raise Not_found
           with
             Not_found ->
             fname
         in
         let stmt' = Fcall (fname',ee',tpRet,tpPrm,loc) in
         _stmtOut := [stmt']
      | FPcall (fname,pos,ee,tpRet,tpPrm,loc) ->
         let ee' = List.map (Exp.subst_elim_AstAnd sub) ee in
         let fname' =
           try
             match List.assoc fname sub with
             | Exp.Lval (Exp.Var (f,_)) -> f
             | _ -> raise Not_found
           with
             Not_found ->
             fname
         in
         let stmt' = FPcall (fname',pos,ee',tpRet,tpPrm,loc) in
         _stmtOut := [stmt']
      | Return (e,loc) ->
         let e' = Exp.subst_elim_AstAnd sub e in
         let stmt' = Return (e',loc) in
         _stmtOut := [stmt']
      | Lbl (label,_,loc) -> ()
      | Break loc -> ()
      | Continue loc -> ()
      | Fail loc -> ()
      | Unknown loc -> ()
      | Block (stmtL,loc) ->
         _stmtOut := [];
         for i = 0 to List.length stmtL - 1 do
           let (vv1,sub1,stmt1) = subst_elim_AstAnd !_vvOut !_subOut (List.nth stmtL i) in
           _vvOut := vv1;
           _subOut := sub1;
           _stmtOut := stmt1 :: !_stmtOut
         done;
         _stmtOut := [Block (List.rev !_stmtOut,loc)]
    end;
    (!_vvOut,!_subOut,List.hd !_stmtOut)
         

  (* local transformation *)
  (* f_exp is a transformation on expressions *)
  (* transfrom_exp applies f_exp homomorphically *)
  let transform_exp (f_lval,f_exp) stmt = 
    let ff = (f_lval,f_exp) in
    let rec aux stmt0 = 
    match stmt0 with
    | Skip -> Skip
    | Decl (decl,loc) ->
       let decl' = Decl.transform_exp ff decl in
       Decl (decl',loc)
    | Asgn (lval,e,loc) ->
       let lval' = f_lval lval in
       let e' = f_exp e in
       Asgn (lval',e',loc)
    | Malloc (x,tp,e,loc) ->
       let e' = f_exp e in
       Malloc (x,tp,e',loc)
    | Free (e,loc) ->
       let e' = f_exp e in
       Free (e',loc)
    | Block (stmtL,loc) ->
       let stmtL' = List.map aux stmtL in
       Block (stmtL',loc)
    | If (b,stmtThen,stmtElse,loc) ->
       let b' = Bexp.transform_exp ff b in
       let stmtThen' = aux stmtThen in
       let stmtElse' = aux stmtElse in
       If (b',stmtThen',stmtElse',loc)
    | While (b,bb,stmtBody,loc) ->
       let b' = Bexp.transform_exp ff b in
       let bb' = List.map (Bexp.transform_exp ff) bb in
       let stmtBody' = aux stmtBody in
       While (b',bb',stmtBody',loc)
    | Fcall (fname,ee,tpRet,tpPrm,loc) ->
       let ee' = List.map f_exp ee in
       Fcall (fname,ee',tpRet,tpPrm,loc)
    | FPcall (fname,pos,ee,tpRet,tpPrm,loc) ->
       let ee' = List.map f_exp ee in
       FPcall (fname,pos,ee',tpRet,tpPrm,loc)
    | Return (e,loc) ->
       let e' = f_exp e in
       Return (e',loc)
    | Lbl (label,varL,loc) -> Lbl (label,varL,loc)
    | Break loc -> Break loc
    | Continue loc -> Continue loc
    | Fail loc -> Fail loc
    | Unknown loc -> Unknown loc
    in
    aux stmt

  let subst_elim_AstAnd_toplevel substPtr stmt =
    (*
    let vv1 = av stmt in
    let vv2 = List.flatten @@ List.map (fun (v,e) -> v :: (Exp.av e)) substPtr in
    let vv = union vv1 vv2 in
     *)
    let vv = unionL (List.map (fun (_,e) -> Exp.av e) substPtr) in
    let (_,subst,stmtSubst) = subst_elim_AstAnd vv substPtr stmt in
    stmtSubst

end
;;

module Structure = struct
  (* This module corresponds to Faisal's Structure in vcpTranslate.ml *)

(* Faisal's one
  type t = string * (Var.t * Term.t) list * (bytes * Var.t list) option
 *)
  (* (NAME, [f1;f2]) is "struct NAME { f1,f2 }" *)
  type t = bytes * (bytes * Exp.tp) list
    
  let to_string (s : t) =
    let (sname,sbody) = s in
    let f (fld,tp) =
      let tp' = Exp.to_string_tp tp in
      fld ^ "<" ^ tp' ^ ">"
    in
    let sbody' = string_of_list f "; " sbody in
    sname ^ " { " ^ sbody' ^ "}"

  let print (s : t) = print_string (to_string s)
    
  let println (s : t) = print_endline (to_string s)    

  let getFields (s : t) : (bytes * Exp.tp) list = snd s
                      
  let getType (s : t) fld =
    let fields = getFields s in
    try
      List.assoc fld fields
    with
      Not_found ->
      begin
        print_error Locs.dummy ("Struct.getType: No field " ^ fld ^ " in the structure" );
        []
      end
                      
end
;;


module TopDecl = struct

  type t =
    | NA of Locs.t

    (* statement at the toplevel *)
    | S of Stmt.t * Locs.t

    (* tp f(param) P : function decl. *)
    | F of Exp.tp * bytes * Decl.t list * Stmt.t * Locs.t

         
  let to_string prompt d =
    match d with
    | NA _ -> prompt ^ "NA"
    | S (stmt,loc) -> Stmt.to_string prompt 0 stmt
    | F (tp,f,prm,body,loc) ->
       let tp' = Exp.to_string_tp tp in
       let body' = Stmt.to_string "" 1 body in
       let prm' = string_of_list (Decl.to_string 0) ", " prm in
       prompt ^ tp' ^ " " ^ f ^ "(" ^ prm' ^ ")\n" ^ body'
       
  let print d = print_string (to_string "" d)
              
  let println d = print_endline (to_string "" d)    

  let lookup_funcdef fname d =
    match d with
    | F (tp,f,prm,body,_) when f = fname -> [(tp,fname,prm,body)]
    | _ -> []
         
end
;;

module Program = struct

  type t = TopDecl.t list
         
  let to_string prompt p = string_of_list (TopDecl.to_string prompt) "\n\n" p
                  
  let print p = print_string (to_string "" p)
              
  let println p = print_endline (to_string "" p)    

  let lookup_funcdef fname p =
    List.map (TopDecl.lookup_funcdef fname) p
                
end
;;

module Module = struct
  (* This module corresponds to Faisal's VcpAllC.t *)
  
  type filename = bytes
  type fullpath = bytes
  type strAliases = bytes V.t
  type t = filename * fullpath * Structure.t V.t * strAliases * Program.t

  let to_string (m : t) =
    let (filename,fullpath,structureV,aliasV,prog) = m in
    let prog' = Program.to_string "" prog in
    let strV' = string_of_V (fun _ s -> Structure.to_string s) "\n" structureV in
    "MODULE: " ^ fullpath ^ "\n" ^ strV' ^ "\n\n" ^ prog'

  let print (m : t) = print_string (to_string m)
    
  let println (m : t) = print_endline (to_string m)

  let lookup_funcdef fname (m : t) =
    let (filename,path,strV,aliasV,prog) = m in
    match Program.lookup_funcdef fname prog with
    | [] -> []
    | info ->
       List.map (fun q -> (filename,path,q)) info
      
end
;;
