module Klocs = Csyntax.Locs
module Kexp = Csyntax.Exp
module Kbexp = Csyntax.Bexp
module Kdecl = Csyntax.Decl
module Kinit = Csyntax.Init
module Kstmt = Csyntax.Stmt
module Kprogram = Csyntax.Program
module KtopDecl = Csyntax.TopDecl
module Kmodule = Csyntax.Module
module Kstructure = Csyntax.Structure
module C = Csyntax

module Fmodule = VcpAllC
            
module FPval = Fpsyntax2.Val
module FPsh = Fpsyntax2.StoreHeap
module FPstate = Fpsyntax2.State
module V = Map.Make(Bytes)
(*module FPwhite = Fpsyntax2.WhiteCandidates*)
module M = Mymem
;;

open Tools
module O = FpOption.Option
;;
let checkLoc linenum loc =
  let (_,num) = loc in
  linenum = num
;;
let skipFuncL = []
;;
let isDebugFun fname =
  let debugFunL = ["__EVAL";"__COMMENT";"__SHOW";"_QUIT"] in
  List.mem fname debugFunL
;;

type field = bytes


(* For checking function pointer returning functions *)
let updateRetFunList slacDataDir recflag tpRet fname =
  match Kexp.isFpType tpRet,recflag with
  | false,_ -> ()
  | true,true ->
     print_endline (fname ^ " returns a function pointer (added to the FP-function list)");
     let fpretFuncs: bytes list = Ftools.read_file (slacDataDir ^ "/Fpa/fpretFuncs") in
     let fpretFuncs' = Tools.union fpretFuncs [fname] in
     Ftools.write_file (slacDataDir ^ "/Fpa/fpretFuncs") fpretFuncs'
  | true,false ->
     print_endline (fname ^ " returns a function pointer (added to the FP-function-Rec list)");     
     let fpretFuncsR: bytes list = Ftools.read_file (slacDataDir ^ "/Fpa/fpretFuncsR") in
     let fpretFuncsR' = Tools.union fpretFuncsR [fname] in
     Ftools.write_file (slacDataDir ^ "/Fpa/fpretFuncsR") fpretFuncsR'
;;


           
(* Global Information *)
(* Funcp refers this info during analysis *)
module GlobalInfo = struct
  
  type funTable = (bytes * int * int) V.t (* { (key=funName, value=(modname,mod_id,pos)) } *)  
  type structInfo = Kstructure.t V.t (* { (key=strName, value=(strName,[fields])) } *)
  type strAliases = bytes V.t (* (alias,strName) *)
  type funModule = int * bytes * Kprogram.t
    
  type t =
    {
      mutable structs : structInfo; (* Struct declarations *)
      mutable funtable : funTable; (* Function definitions *)
      mutable straliases : strAliases; (* aliases of structs *)
      mutable missfunL : bytes list; (* list of missing functions *)
      mutable fundefdir : bytes; (* function definition directory *)
      mutable slacDataDir : bytes;
      mutable missingFP : int;
      mutable fpaFunProfileDir : bytes;
      mutable fmodules : Fmodule.t list;
    }

  let init () : t =
    {
      structs = V.empty;
      funtable = V.empty;
      straliases = V.empty;
      missfunL = [];
      fundefdir = "";
      slacDataDir = "";
      missingFP = 0;
      fpaFunProfileDir = "";
      fmodules = [];
    }

  let reset gi =
      gi.structs <- V.empty;
      gi.funtable <- V.empty;
      gi.straliases <- V.empty;
      gi.missfunL <- [];
      gi.fundefdir <- "";
      gi.slacDataDir <- "";
      gi.missingFP <- 0;
      gi.fpaFunProfileDir <- "";
      gi.fmodules <- []
                       
  let isDefinedFun gi fname = V.mem fname gi.funtable

  let lookup_funmodule gi mod_id : int * bytes * Kprogram.t =
    let mod_id' = string_of_int mod_id in
    let funmod: funModule = Ftools.read_file (gi.fundefdir ^ "/" ^ mod_id') in
    funmod

  let lookup_fundef gi (mod_id,pos) : bytes * KtopDecl.t =
    let (_,modname,fundefL) = lookup_funmodule gi mod_id in
    (modname,List_mes.nth "lookup_fundef" fundefL pos)

  let lookup_structure gi structname : Kstructure.t = 
    if V.mem structname gi.structs then
      V_mes.find "lookup_structure" structname gi.structs
    else
      raise (Ftools.StError ("Struct Not Found Exception: " ^ structname))

  let getFundefBody gi fname =
    match findItemOptionV fname gi.funtable with
    | None -> None
    | Some (_,mod_id,pos) ->
       let (modulename,fundef) = lookup_fundef gi (mod_id,pos) in
       match fundef with
       | KtopDecl.F (tpRet,_,declPrms,stmtBody,_) -> Some (tpRet,declPrms,stmtBody)
       | _ -> None
                       
end
;;
module GI = GlobalInfo
;;
(* Global Information *)
let gi = GI.init ()
;;

(* Union of structs *)
(* expected behavior is the following *)
(* { (str0,[]),(str1,[f:0]) } union { (str0,[g:1]),(str2,[h:0]) } is { (str0,[g:1]),(str1,[f:0]),(str2,[h:0]) } *)
let struct_union (str0: Kstructure.t V.t) str1 =
  let _straliasV = ref V.empty in (* (alias,strName) *)
  let merge_fields fldTpL0 fldTpL1 =
    let _res = ref [] in
    let zipFldTpL = List_tailrec.zip_assoc [] fldTpL0 fldTpL1 in
    for i = 0 to List.length zipFldTpL - 1 do
      let (fld,(tp1,tp2)) = List.nth zipFldTpL i in
      match Kexp.getStructName_opt tp1,Kexp.getStructName_opt tp2 with
      | None,_ ->
         _res := (fld,tp2) :: !_res
      | _,None ->
         _res := (fld,tp1) :: !_res
      | Some str1,Some str2 when str1 = str2 ->
         _res := (fld,tp1) :: !_res
      | Some str1,Some alias ->
         _straliasV := V.add alias str1 !_straliasV;
         _res := (fld,tp1) :: !_res
    done;
    !_res
  in
  let f strName (str0_opt: Kstructure.t option) str1_opt =    
    match str0_opt,str1_opt with
    | Some (_,fldTpL0),Some (_,fldTpL1) ->
       (*
       if strName = debugStruct
       then
         let str0 = (strName,fldTpL0) in
         let str1 = (strName,fldTpL1) in
         Kstructure.println str0;
         Kstructure.println str1
       else ();
        *)
       let fldTp = merge_fields fldTpL0 fldTpL1 in
       Some (strName,fldTp)
    | None,Some str1 ->
       (*
       if strName = debugStruct
       then Kstructure.println str1
       else ();
        *)
       str1_opt
    | Some str0,None ->
       (*
       if strName = debugStruct
       then Kstructure.println str0
       else ();
        *)
       str0_opt
    | None,None -> None
  in
  (V.merge f str0 str1, !_straliasV)
;;

let funtable_union ftbl0 ftbl1 =
  let f func pos0_opt pos1_opt =
    match pos0_opt,pos1_opt with
    | None,_ -> pos1_opt
    | _,None -> pos0_opt      
    | Some (cfile1,_,_),Some (cfile2,_,_) ->
       (* This case is ignored since this "func" would be an external (library function). *)
       None
  in
  V.merge f ftbl0 ftbl1
;;


module FpPos = struct

  type t = ((bytes * bytes * int) * FPval.t) list

  let empty = []
         
  let print fppos =
    let print_f_one ((funF,fp,pos),v) =
      print_string' @@ "(" ^ fp ^ "!" ^ (string_of_int pos) ^ "@" ^ funF ^ ")->";
      FPval.print v
    in
    print_list print_f_one "," fppos

  let println fppos =
    print fppos;
    print_endline ""

  (* substitution of place-holders in fppos 
    sub = [ ([x],v1); ([s->f],v2); ($0,v3) ]
    (F1,fp1,pos1,Union([x],v)) --> (F1,fp1,pos1,Union([x],v,v1))
   *)
  let subst_sh aliases sh fppos =
    let (s,h) = sh in 
    let evalPh p =     (* eval a place-holder *)
      let p' = Bytes.sub p 1 ((Bytes.length p)-2) in (* "[aaaa]" -> "aaaa" *)
      match cut_string2 "->" p' with (* [varname] or [strName;fld] *)
      | [v] ->
         begin
           match List.assoc_opt v (FPsh.fp_of s) with
           | Some value1 -> value1 
           | None -> FPval.none
         end
      | strName::fld::[] ->
         begin
           match FPsh.lookup_h_field_fp ("",0) aliases sh strName fld with
           | Some value1 -> value1
           | None -> FPval.none
         end
      | _ -> failwith ""
    in
    let substVal value =
      List.fold_left
        (fun value0 u ->
          match u with
          | FPval.Ph p -> FPval.union value0 (FPval.union (evalPh p) [u])
          | _ -> FPval.union value0 [u]
        )
        FPval.none
        value
    in
    List.map 
      (fun (fnameFpPos,value0) -> (fnameFpPos,substVal value0))
      fppos

  let subst aliases r fppos =
    match r with
    | FPstate.None -> fppos
    | FPstate.SH sh -> subst_sh aliases sh fppos
                     
(*
  let subst aliases r fppos =
    let parseVar v =
      let v' = Bytes.sub v 1 ((Bytes.length v)-2) in (* "[aaaa]" -> "aaaa" *)
      cut_string2 "->" v' (* [varname] or [strName;fld] *)
    in
    let substOne (s,h) ((fname,fp,pos),value) =
      print_string' "CURRENT VAL: " ; FPval.println value;
      match value with
      | FPval.Ph v when List.length (parseVar v) = 1 ->
         print_endline "CASE-1";
         let vv = parseVar v in
         let gvar = List.nth vv 0 in
         (* hoge *)
         print_endline ("SUBSTITUTION: " ^ fname ^ " " ^ fp ^ " of " ^ v ^ " :: " ^ gvar);
         (* hoge *)         
         begin
           match List.assoc_opt gvar (FPsh.fp_of s) with
           | Some value1 ->
              print_endline "CASE-1a";
              (* hoge *)
              print_endline " SUBST execution";
              FPval.print value;              
              print_endline " becomes ";
              FPval.print value1;
              print_endline "";
              (* hoge *)         
              ((fname,fp,pos),value1)
           | None ->
              print_endline "CASE-1b";
              print_endline " SUBST NOT executed";
              ((fname,fp,pos),value)
         end
      | FPval.Ph v when List.length (parseVar v) = 2 ->
         print_endline "CASE-2";         
         let vv = parseVar v in
         let strName = List.nth vv 0 in
         let fld = List.nth vv 1 in
         (* hoge *)
         print_endline ("SUBSTITUTION: " ^ v ^ " :: " ^ strName ^ "->" ^ fld);
         (* hoge *)         
         begin
           match FPsh.lookup_h_field_fp ("",0) aliases (s,h) strName fld with
           | Some value1 ->
              print_endline "CASE-2a";
              (* hoge *)
              print_endline " SUBST execution";
              FPval.print value;              
              print_string' " --> becomes --> ";
              FPval.print value1;
              print_endline "";
              (* hoge *)         
              ((fname,fp,pos),value1)
           | None ->
              print_endline "CASE-2b";              
              print_endline " SUBST NOT executed";
              ((fname,fp,pos),value)
         end
      | FPval.Ph v -> failwith ("Fppos.substOne: " ^ v)
      | _ ->
         print_endline "CASE-3";
         ((fname,fp,pos),value)
    in
    match r with
    | FPstate.None -> fppos
    | FPstate.SH sh -> List.map (substOne sh) fppos
 *)

  let eval (fppos: t) (func,fp,pos) =
    match List.assoc_opt (func,fp,pos) fppos with
    | Some value -> value
    | None -> [FPval.Fname[]]
                     
  let finalize (fppos : t) : t =
    let finalizeValue value =
      let (fnameL,snameL,_) = FPval.split value in
      FPval.combine (fnameL,snameL,[])
    in
    let finalizeOne ((fname,fp,pos),value) =
      let value' = finalizeValue value in
      ((fname,fp,pos),value')
    in
    List.map finalizeOne fppos
                     
  let toOutput fppos : ((bytes * bytes * int) * bytes list) list =
    List.map
      (fun ((fname,fp,pos),value) ->
        let (fnameL,_,_) = FPval.split value in
        ((fname,fp,pos),fnameL)
      )
      fppos
    
end
;;


(* An analyzer contains local information during funcp analysis *)
(* This may be copied (e.g. IF-branch) *)
module Analyzer = struct

  type mode = NOMODE
            | GLOBAL (* global variable Analysis *)
            | FPA (* main analysis *)
            | MOD (* modular analysis *)
            | MODREC (* modular analysis for recursive functions *)            
            | MODREC0 (* Pre Modular-analysis for Recursive functions *)
  type t =
    {
      mutable funstack : bytes list;
      (* stack of function names (the topmost name is the current function in the analysis) *)
      mutable whilestack : bool list;
      (* [false;false;true] *)
      (* true and false mean 'changed' and 'unchanged', respectively *)
      (* nested while1 (while2 (while3 ...) ) --> [flagWhile3;flagWhile2;flagWhile1] *)
      (* while3 is unchanged, while2 is unchanged, while1 is changed *)
      mutable localVarCtr : int;
      mutable missingFunlist : bytes list;
      mutable knownList : VcpAllC.rec_t list;
      mutable currentFunc : bytes;
      mutable mode : mode;
      mutable skipFunclist : bytes list; (* Skip function list for ModRec0-mode *)
      mutable fppos : FpPos.t;
      mutable nth : int; (* nth execution (nth=0,1,2) *)
      mutable noMod : bool; (* modular analysis flag: true=ON (default), false=OFF *)
      mutable twice : bool; (* modular analysis flag: true=ON (default), false=OFF *)
    }

  let println_fppos az = FpPos.println az.fppos
    
  let inclLocalVarCtr az =
    az.localVarCtr <- az.localVarCtr + 1
  let show_funstack az =
    print_string' "@@ ";
    print_list print_string' " > "  az.funstack;
    print_endline ""
    
  let add_show_funstack fname az =
    let fstack = List.rev (fname :: az.funstack) in
    print_string' "@@ ";
    print_list print_string' " > "  fstack;
    print_endline ""
    
  let init fname : t =
    {
      funstack = [fname];
      whilestack = [false];
      localVarCtr = 0;
      missingFunlist = [];
      currentFunc = fname;
      knownList = [];      
      mode = NOMODE;
      skipFunclist = [];
      fppos = [];
      nth = 0;
      noMod = false;
      twice = false;
    }

  let reset mode az =
    az.funstack <- [];
    az.whilestack <- [false];
    az.localVarCtr <- 0;
    az.currentFunc <- "";
    az.mode <- mode;
    az.skipFunclist <- []

  let isKnown az fname =
    let rec aux knownlist =
      match knownlist with
      | [] -> false
      | (VcpAllC.NONREC f)::_ when f = fname -> true
      | (VcpAllC.REC fnameL)::_ when List.mem fname fnameL -> true
      | _ :: knownlist1 -> aux knownlist1
    in
    aux az.knownList
      
  let knownlist_flatten az =
    List.fold_left
      (fun fnameL frec ->
        match frec with
        | VcpAllC.NONREC f -> f :: fnameL
        | VcpAllC.REC fnameL1 -> union fnameL1 fnameL
      )
      []
      az.knownList
  let push_whilestack az =
    az.whilestack <- false :: az.whilestack

  let pop_whilestack az =
    match az.whilestack with
    | [] -> failwith "WhileStack.pop"
    | res::tl ->
       az.whilestack <- tl;
       res
    
  let update_whilestack az flag =
    match flag with
    | true -> (* changed *)
       az.whilestack <- true :: (List.tl az.whilestack)
    | false -> (* unchanged *)
       ()

  let show_whilestack az =
    print_string' "[";
    print_list (function true -> print_string' "TRUE" | false -> print_string' "FALSE") "," az.whilestack;
    print_endline "]"

  let evalFppos (az: t) fname fp pos =
    try
      List.assoc (fname,fp,pos) az.fppos
    with
      Not_found -> FPval.none
    
end
;;
module AZ = Analyzer
;;
let az = AZ.init ""
;;

let azUpdateFppos loc fname fp pos value =
  let order_fppos (v1,fp1,n1) (v2,fp2,n2) =
    if v1 > v2 || (v1 = v2 && fp1 > fp2) || (v1 = v2 && fp1 = fp2 && n1 > n2) then 1 else
      if v1 < v2 || (v1 = v2 && fp1 < fp2) || (v1 = v2 && fp1 = fp2 && n1 < n2) then -1 else 0
  in
  let fppos1 = List.filter (fun ((fname1,_,_),_) -> fname = fname1) az.AZ.fppos in
  let fppos1_other = List.filter (fun ((fname1,_,_),_) -> fname <> fname1) az.AZ.fppos in    
  (*  let v' = FPval.subst [] value in (* replace [fp] by [] *) *)
  let fppos1' = updateListOrder order_fppos fppos1 (fname,fp,pos) value in
  let fppos2 = Tools.union fppos1' fppos1_other in
  az.AZ.fppos <- fppos2
;;
  
let azUpdateFppos_many loc fnameFpPosValL =
  List.iter (fun (fname,fp,pos,v) -> azUpdateFppos loc fname fp pos v) fnameFpPosValL
;;

let azShowFppos_filter (fname,fp,pos) =
  let myPrint () = print_string' (fname ^ "@" ^ fp ^ "!" ^ (string_of_int pos) ^ "->") in
  match List.assoc_opt (fname,fp,pos) az.AZ.fppos with
  | None ->
     myPrint ();
     print_endline "NOENTRY"
  | Some value ->
     myPrint ();
     FPval.println value
;;

let print_message opt sym loc mes =
  let mode =
    let nth = if az.AZ.nth = 1 then "" else "-"^(string_of_int az.AZ.nth) in
    let modestr = 
      match az.AZ.mode with
      | AZ.NOMODE -> ""
      | AZ.GLOBAL -> "GLOBAL"
      | AZ.FPA -> "FPA"
      | AZ.MOD -> "MOD"
      | AZ.MODREC -> "MODREC"
      | AZ.MODREC0 -> "MODREC0" (* Pre-Modular analysis for Recursive functions *)
    in
    modestr ^ nth
  in
  let fname = az.AZ.currentFunc in  
  let funLoc =
    match fst loc,fname with
    | "","" -> ""
    | "",_ -> " " ^ fname
    | _,"" -> " " ^ (Klocs.to_string loc)
    | _,_ -> " " ^ fname ^ " " ^ (Klocs.to_string loc)
  in
  match opt with
  | "DEBUG" ->
     Ftools.pf_s "FPAdebug" print_endline ("[" ^ sym ^ " " ^ mode ^ funLoc ^ "] " ^ mes)
  | "ALWAYS" ->
     print_endline ("[" ^ sym ^ " " ^ mode ^ funLoc ^ "] " ^ mes)
  | _ -> failwith "print_message"
    
;;


let print_mes ?(opt="DEBUG") = print_message opt "_"
;;
let print_err = print_message "ALWAYS" "E"
;;
let print_warn = print_message "ALWAYS" "W"
;;

(* tp is assumed to be a function-pointer type *)
let rec initFpType loc sh (init : Kinit.t) : FPval.t =
  try
    match init with
    | Kinit.S (Kexp.Func fname) -> [FPval.Fname [fname]]
    | Kinit.M [Kinit.S (Kexp.Func fname)] -> [FPval.Fname [fname]]
    | Kinit.M _ -> raise Exit
    | Kinit.S (Kexp.Lval lval) ->
       let fname = Kexp.getVarName_lval lval in
       [FPval.Fname [fname]]
    | _ -> raise Exit
  with
    _ ->
    FPval.none
;;

let initVal tp =
  match Kexp.hasFunc tp,Kexp.hasStruct tp with
  | true,_ -> [FPval.Fname []]
  | false,true ->
     let structName =
       try
         Kexp.getStructName tp
       with
         _ -> (print_endline "failed to get struct name"; failwith "")
     in
     [FPval.Sname structName]
  | _ -> FPval.none
;;

(* Not allocating allocTypeFP: this produces a unmerged heap *)
(* tp should be a struct type without the Array-attribution *)
let rec allocTypeFP loc sh (tp,iDim) (init : Kinit.t) : FPsh.preheap = 
  let print_it_lazy () =
    let tp1 = if iDim = [] then tp else tp @ [Kexp.ARRAY (List.map (fun n->Kexp.Int n) iDim)] in
    Ftools.pf_s "FPAdebug" print_endline
      ("-- allocTypeFP(tp:" ^
         (Kexp.to_string_tp tp1) ^
           ", init:" ^
             (Kinit.to_string init) ^
               ")")
  in
  let straliases = gi.GI.straliases in
  let funtable = gi.GI.funtable in
  let strV = gi.GI.structs in
  Ftools.pf_s "FPAdebug" print_it_lazy ();
  match Kexp.hasStruct tp,iDim with
  (* Non-struct case *)    
  | false,_ -> failwith "allocTypeFP: unexpected type (non-struct case)"
  (* Size zero *)
  | _,[] ->
     Ftools.pf_s "FPAdebug" print_endline "-- allocTypeFP case-0";
     FPsh.preheap_empty (* empty preheap *)
  (* An array of structs *)            
  | _,d::_ when d > 0 || d = -2 -> (* d=-2: missing size *)
     Ftools.pf_s "FPAdebug" print_endline "-- allocTypeFP case-1";     
     let iDim1 = if List.tl iDim = [] then [-1] else List.tl iDim in
     let initL =
       match init with
       | Kinit.None ->
          List.map (fun _ -> Kinit.None) (genLst d)
       | Kinit.M initL1 when List.length initL1 = d || d = -2 ->
          initL1
       | _ ->
          print_warn loc @@ "allocTypeFP: unexpected Init-1 (skip with empty heap)";
          FPsh.preheap_empty (* empty preheap *)
     in
     List.fold_left (fun h init -> h @ (allocTypeFP loc sh (tp,iDim1) init)) FPsh.preheap_empty initL

  (* Single struct *)
  | _,d::_ -> (* only [-1] comes *)
     Ftools.pf_s "FPAdebug" print_endline "-- allocTypeFP case-2";
     let structName =
       try
         Kexp.getStructName tp
       with
         _ -> (print_endline "failed to get struct name";failwith "")
     in
     let realStrName = FPsh.getRealStrName straliases structName in
     let fldTpL = snd (GI.lookup_structure gi realStrName) in
     let l = List.length fldTpL in
     let initL =
       match init with
       | Kinit.M initL1 when List.length initL1 = l -> initL1
       | _ -> List.map (fun _ -> Kinit.None) (genLst l)
     in

     let fldTpInitL = List.map (fun ((fld,tp),init) -> (fld,tp,init)) (zipLst fldTpL initL) in
     let mkPreHeapBody (fld,tp,init) =
       match Kexp.isStructType tp, (Kexp.isFpType tp || Kexp.isFunType tp),init with
       | true,true,_ -> failwith "allocTypeFP: unexpected type-1"
       | true,false,_ ->
          let sname = FPsh.getRealStrName straliases (Kexp.getStructName tp) in
          (fld,[FPval.Sname sname])
       | false,true,Kinit.None ->
          (fld,[FPval.Fname []])
       | false,true,Kinit.S exp ->
          let value = FPsh.evalCExpFp loc strV straliases funtable sh exp in
          (fld,value)
       | false,true,_ -> failwith "allocTypeFP: unexpected Init-3"
       | false,false,_ ->
          (fld,FPval.none)
     in
     let preheap0: FPsh.preheap = [ (realStrName, List.filter (fun (_,v) -> v <> FPval.none) (List.map mkPreHeapBody fldTpInitL)) ] in
     let _h = ref preheap0 in
     for i = 0 to l - 1 do
       let (_,tp_i,init_i) = List.nth fldTpInitL i in
       if Kexp.isStructType tp_i
       then
         let (tp_i',eDim_i') = Kexp.extract_dim tp_i in
         let iDim_i' = if eDim_i' <> [] then List.map (FPsh.evalCExpInt loc sh) eDim_i' else [-1] in
         _h := !_h @ (allocTypeFP loc sh (tp_i',iDim_i') init_i)
       else ()
     done;
     !_h
;;




exception CannotSkip
;;
(*------------------
FPR,FPM,FN,FPO,RET,HISTORY
------------------*)
module FunProfile = struct

  type fpr_t = Kexp.t list
  type fpm_t = Kexp.lval list
  type fn_t = bytes list
  type fpc_t = bytes list 
  type fpoL_t = (Kexp.lval * FPval.t) list
  type fpposL_t = (bytes * bytes * int * FPval.t) list (* (F,fp,n,{F1,[fp]}) is FPO(n) = {F1,[fp]} *)
  type fnames_t = bytes list              
  type retVal_t = FPval.t
  type argRecord_t = fnames_t list (* argument record: F(t1,t2) -> [sh(t1),sh(t2)] *)
  type fpRefRecord_t = (Kexp.t * fnames_t) list (* fp-ref.rec.: t->fp with its value fnameL is saved as (t->fp,fnameL) *)
  type history_t = (argRecord_t * fpRefRecord_t) list
  type t = fpr_t * fpm_t * fn_t * retVal_t * fpoL_t * fpposL_t * history_t

  let empty = ([],[],[],FPval.none,[],[],[])
         
  let init () : t = empty
  let print_fpr (fpr: fpr_t) = List.iter Kexp.println fpr

  let print_fpm (fpm: fpm_t) = List.iter Kexp.println_lval fpm
                    
  let print_fn (fn: fn_t) = List.iter print_endline fn

  let print_retVal (retVal: retVal_t) = FPval.println retVal

  let print_fpoL (fpoL: fpoL_t) =
    List.iter
      (fun (lval,v) ->
        print_string' "(";
        Kexp.print_lval lval;
        print_string' ",";
        FPval.print v;
        print_endline ")";
      )
      fpoL

  let print_fpposL (fpposL: fpposL_t) =
    List.iter
      (fun (fname,fp,n,v) ->
        print_string' ("((" ^ fname ^ "," ^ fp ^ "!" ^ (string_of_int n) ^ ")->");
        FPval.print v;
        print_endline ")";
      )
      fpposL
    
  let print_history (history : history_t) =
    List.iter
      (fun (argRec,fpRefRec) ->
        print_string' "Args: ";
        print_list
          (fun fnameL -> print_string' "{"; (print_list print_string' "," fnameL); print_string' "}") "," argRec;
        print_string' "\nRefRecords: ";
        print_list 
          (fun (e,fnameL) ->
            print_string' "(";
            Kexp.print e;
            print_string' ",{";
            print_list print_string' "," fnameL;
            print_string' "})";
          )
          ","
          fpRefRec;
        print_endline ""
      )
      history

  let print prof =
    let (fpr,fpm,fn,retVal,fpoL,fpposL,history) = prof in
    print_endline "[FPR]";
    print_fpr fpr;
    print_endline "[FPM]";
    print_fpm fpm;
    print_endline "[FN]";
    print_fn fn;
    print_endline "[retVal]";
    print_retVal retVal;
    print_endline "[fpoL]";
    print_fpoL fpoL;
    print_endline "[fpposL]";
    print_fpposL fpposL;    
    print_endline "[history]";
    print_history history

  let println_opt prof_opt =
    match prof_opt with
    | None -> ()
    | Some prof -> print prof
    
  let rec isFpHolder exp = (* exp's type must be a function-pointer type *)
    match exp with
    | Kexp.Lval lval -> isFpHolder_lval lval
    | _ -> false
  and isFpHolder_lval lval = (* lval's type must be a function-pointer type *)
    match lval with
    | Kexp.Var(_,tp) when Kexp.isFpType tp -> true 
    | Kexp.Arrow (_,_,_) -> true
    | Kexp.Ptr _ -> true
    | _ -> false

  let get fname : t =
    try
      let profile : t = Ftools.read_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) in
      profile
    with
      _ ->
      begin
        print_warn ("",0) @@ "Profile of "^fname^" is not found (an empty profile is created)";
        Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) empty;
        empty
      end
         
  let getFprFpmFn fname : fpr_t * fpm_t * fn_t =
    let (fpr,fpm,fn,_,_,_,_) = get fname in
    (fpr,fpm,fn)

  let getFpr fname : fpr_t =
    let (fpr,_,_,_,_,_,_) = get fname in
    fpr

  let getFpm fname : fpm_t =
    let (_,fpm,_,_,_,_,_) = get fname in
    fpm
    
  let getHistory fname : history_t =
    let (_,_,_,_,_,_,history) = get fname in
    history

  (* size of a profile *)
  let getSize (prof : t) =
    let (fpr,fpm,fn,retVal,fpoL,fpposL,_) = prof in
    let val_size v =
      let (fnameL,_,_) = FPval.split v in
      List.length fnameL
    in
    let retSize = val_size retVal in
    let fpoSize = List.fold_left (fun n (_,fpval) -> n+(val_size fpval)) 0 fpoL in
    let fpposSize = List.fold_left (fun n (_,_,_,fpval) -> n+(val_size fpval)) 0 fpposL in
    let fprSize = List.length fpr in
    let fpmSize = List.length fpm in
    fprSize + fpmSize + fpoSize + fpposSize + retSize

  let getSizeL profL = List.fold_left (fun n prof -> n+(getSize prof)) 0 profL
  let load_show fnameL =
    List.iter
      (fun fname ->
        print_endline "";
        print_endline ("PROFILE of " ^ fname);
        print (get fname)
      )
      fnameL

  let updateHistory_save loc fname sh eeArgs (prof_opt : t option) : t option =
    let sameRecords fpRefRecord1 fpRefRecord2 =
      if List.length fpRefRecord1 <> List.length fpRefRecord2
      then false
      else
        let size1 = List.fold_left (fun n (_,fnameL) -> n+(List.length fnameL)) 0 fpRefRecord1 in
        let size2 = List.fold_left (fun n (_,fnameL) -> n+(List.length fnameL)) 0 fpRefRecord2 in
        size1 = size2
    in
    let sameArgFnameL argFnameL1 argFnameL2 =
      let size1 = List.fold_left (fun n fnameL -> n+(List.length fnameL)) 0 argFnameL1 in
      let size2 = List.fold_left (fun n fnameL -> n+(List.length fnameL)) 0 argFnameL2 in
      size1 = size2
    in
    let rec isNew (argFnameL,fpRefFnameL) history =
      try
        match history with
        | [] -> true
        | (argFnameL1,fpRefFnameL1)::history1 ->
           if (sameArgFnameL argFnameL argFnameL1) && (sameRecords fpRefFnameL fpRefFnameL1)
           then raise Exit
           else isNew (argFnameL,fpRefFnameL) history1
      with
        Exit -> false
    in
    match prof_opt with
    | None -> None
    | Some (fpr,fpm,fn,ret,fpoL,fpposL,history) ->
       let eeArgs' = List.filter Kexp.isFpFun eeArgs in
       let argFnameL =
         List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) eeArgs' in
       let fpRefFnameL =
         List.map
           (fun e ->
             let fnameL = FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh e in
             (e,fnameL))
           fpr
       in
       let history' =
         if isNew (argFnameL,fpRefFnameL) history
         then (argFnameL,fpRefFnameL)::history
         else history
       in
       let prof = (fpr,fpm,fn,ret,fpoL,fpposL,history') in
       Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) prof;
       Some prof

  let updateFn loc fnameFnL prof_opt =
    match prof_opt with
    | None -> None
    | Some (fpr,fpm,fn,ret,fpoL,fpposL,history) ->
       let fn' = union fnameFnL fn in
       Some (fpr,fpm,fn',ret,fpoL,fpposL,history)

  let updateFpr loc gi prof_opt ee =
    match prof_opt with
    | None -> None
    | Some (fpr,fpm,fn,ret,fpoL,fpposL,history) ->
       let strV = gi.GI.structs in
       let aliases = gi.GI.straliases in
       let eeFpHolder = Kexp.getFpHolderL strV aliases ee in
       let fpr' = union eeFpHolder fpr in
       Some (fpr',fpm,fn,ret,fpoL,fpposL,history)

  let updateFpm loc gi prof_opt lvalL =       
    let updateOne prof lval =
      let (fpr,fpm,fn,ret,fpoL,fpposL,history) = prof in
      let strV = gi.GI.structs in
      let aliases = gi.GI.straliases in
      let eeFpHolder_lval = Kexp.getFpHolder_lval strV aliases lval in
      let fpm' = union eeFpHolder_lval fpm in
      (fpr,fpm',fn,ret,fpoL,fpposL,history)
    in
    match prof_opt with
    | None -> None
    | Some prof ->
       let prof' = List.fold_left (fun prof1 lval1 -> updateOne prof1 lval1) prof lvalL in
       Some prof'
    
  let updateFppos loc gi prof_opt fname fp pos value =
    match prof_opt with
    | None -> None
    | Some (fpr,fpm,fn,ret,fpoL,fpposL,history) ->
       let fpposL_other =
         List.filter (fun (fname1,fp1,pos1,_) -> fname1 <> fname || fp1 <> fp || pos1 <> pos) fpposL
       in
       let fpposL' = 
         match List.filter (fun (fname1,fp1,pos1,_) -> fname1 = fname && fp1 = fp && pos1 = pos) fpposL with
         | [] ->
            (fname,fp,pos,value) :: fpposL_other
         | (_,_,_,value0)::_ ->
            let value1 = FPval.union value0 value in
            (fname,fp,pos,value1) :: fpposL_other
       in
       Some (fpr,fpm,fn,ret,fpoL,fpposL',history)
       
  (* (fpr,fpm,fn,[],[],[],[]) --> (fpr,fpm,fn,retVal,fpoL,fpposL,[]) *)
  let generate_ret_fpo sh fname (profile: t) : t =
    let (fpr,fpm,fn,_,_,fpposL0,_) = profile in
    let loc = ("",[]) in    
    let fpoL : fpoL_t =
      List.map
        (fun lval ->
          let fpVal = FPsh.evalCExpFp_lval loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh lval in
          (lval,fpVal))
        fpm
    in
    let fpposL : fpposL_t =
      List.fold_left
        (fun ls ((f,fp,pos),v) ->
          if f <> fname
          then ls
          else
            match List.assoc_opt (f,fp,pos) (List.map (fun (a,b,c,d)->((a,b,c),d)) fpposL0) with
            | None -> (f,fp,pos,v) :: ls
            | Some v0 ->
               let v1 = FPval.union v v0 in
               (f,fp,pos,v1) :: ls
        )
        []
        az.AZ.fppos
    in

    let retVal =
      let (s,h) = sh in
      FPsh.retVal_of s
      (*
      let ((s_stack,_),h) = sh in
      let (_,retFP,retStruct) = List_mes.hd "generate_ret_fpo: empty store!" s_stack in
      match retFP,retStruct with
      | [],[] -> FPval.None
      | fnameL,[] -> FPval.Fname fnameL
      | [],strName -> FPval.Sname strName
      | _,_ -> failwith "generate_ret_fpo: invalid return value ()"
       *)
    in
    if fpposL = [] then ()
    else
      begin
        Ftools.pf_s "FPAdebug" print_endline "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";
        Ftools.pf_s "FPAdebug" print_endline fname;
        Ftools.pf_s "FPAdebug" print_endline "AAAAAAA";
        Ftools.pf_s "FPAdebug" print_fpposL fpposL0;
        Ftools.pf_s "FPAdebug" print_endline "AAAAAAA";
        Ftools.pf_s "FPAdebug" print_fpposL fpposL;    
        Ftools.pf_s "FPAdebug" print_endline "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";
      end;
    (fpr,fpm,fn,retVal,fpoL,fpposL,[])

  (* mkFpc sh fname = Union{ sh(e) | e in FPR(fname)} union FN(fname) *)
  (* FPC(sh,F) *)
  let mkFpc sh fname : fpc_t =
    let loc = ("",0) in
    let (eeFpr,_,fn) = getFprFpmFn fname in
    let fnameLL = List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) eeFpr in
    unionL (fn :: fnameLL)

  let mkFpcL sh fnameL = unionL (List.map (mkFpc sh) fnameL)
        
  let isWhite fname = if (getFpm fname = []) then true else false
                    
  let isWhiteL fnameL =
    let isWhite_show fname =
      match getFpm fname with
      | [] -> true
      | fpm::_ ->
         print_string' @@ fname ^ " is not WHITE: ";
         Kexp.print_lval fpm;
         false
    in
    List.for_all isWhite_show fnameL

  let subst_fpoL (sub: (bytes * FPval.t) list) fpoL =
    List.map (fun (e,v) -> (e,FPval.subst sub v)) fpoL

  let subst_fpposL (sub: (bytes * FPval.t) list) fpposL =
    List.map (fun (fname,fp,n,v) -> (fname,fp,n,FPval.subst sub v)) fpposL

  let read_many fnameL =
    List.fold_left
      (fun profL fname ->
        let prof : t = Ftools.read_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) in
        profL @ [prof]
      )
      []
      fnameL
        
end
;;

let print_sub sub =
  List.iter
    (fun (x,v) -> print_string' (x ^ ":="); FPval.println v)
    sub
;;  

let skipCheck myModularAnalysis sp_tm loc sh eeArg fname =
  print_mes loc @@ fname ^ " is called";
  Ftools.pf_s "FPAdebug" print_endline "Skip check starts";
  let aliases = gi.GI.straliases in
  let funtable = gi.GI.funtable in
  let strV = gi.GI.structs in
  let checkKnownList fnameL =
    let rec aux fnameL = 
      match fnameL with
      | fname::fnameL1 when List.mem fname az.AZ.missingFunlist ->
         print_mes loc @@ fname ^ " is a missing function (skip)";
         ()
      | fname::fnameL1 when GI.getFundefBody gi fname = None ->
         C.print_warn loc @@ fname ^ " : definition NotFound --> Empty profile is created + added to KnownList";
         az.AZ.missingFunlist <- Tools.union az.AZ.missingFunlist [fname];
         az.AZ.knownList <- (VcpAllC.NONREC fname) :: az.AZ.knownList;
         Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) FunProfile.empty
      | fname::fnameL1 when not (List.mem fname (AZ.knownlist_flatten az)) ->
         print_mes loc (fname ^ " is unknown --> Start Modular analysis");
         az.AZ.mode <- AZ.MOD;         
         myModularAnalysis sp_tm fname;
         aux fnameL1
      | _ ->
         ()
    in
    aux fnameL
  in
  let checkWhite_of_unionX sh fname =
    let _UX = ref (FunProfile.mkFpc sh fname) in (* union of Xi *)
    let _X = ref (FunProfile.mkFpc sh fname) in (* current X *)
    while !_X <> [] do
      _X := setminus (FunProfile.mkFpcL sh !_X) !_UX;
      checkKnownList !_X;
      _UX := union !_X !_UX;
      if List.for_all FunProfile.isWhite !_UX
      then ()
      else
        begin
          Ftools.pf_s "FPAdebug" print_endline "CheckSkip: White check ... NO";
          raise CannotSkip
        end
    done;
    Ftools.pf_s "FPAdebug" print_endline "CheckSkip: White check ... OK"
  in
  let checkHistory sh fname eeArg =
    let fnameL = FunProfile.mkFpc sh fname in (* fnameL = FPC(fname) *)
    let eeFpHold = unionL (List.map FunProfile.getFpr fnameL) in (* eeFpHoldL = Union{ FPR(f) | f in fnameL } *)
    let eeArg' = List.filter Kexp.isFpFun eeArg in
    let fnamesArg = List.map (FPsh.evalCExpFp_fnameL loc strV aliases funtable sh) eeArg' in
    let eFnamesL = List.map (fun w -> (w,FPsh.evalCExpFp_fnameL loc strV aliases funtable sh w)) eeFpHold in
    let history = FunProfile.getHistory fname in    
    let historyCheckOne (fnamesArg0,eFnameL0) =
      let check1 =
        List.for_all
          (fun (fnames_now,fnames_prev) -> subset fnames_now fnames_prev)
          (zipLst fnamesArg fnamesArg0)
      in
      let check2 =
        List.for_all
          (fun (w,fnameL_now) ->
            match List.assoc_opt w eFnameL0 with
            | None -> false
            | Some fnameL_prev ->
               List.length fnameL_now <= List.length fnameL_prev
          )
          eFnamesL
      in
      check1 && check2
    in
    if List.exists historyCheckOne history
    then
      Ftools.pf_s "FPAdebug" print_endline "CheckSkip: History check ... OK"
    else
      begin
        let mes = if history = [] then " (history is empty)" else "" in
        Ftools.pf_s "FPAdebug" print_endline ("CheckSkip: History check ... NO" ^ mes);
        raise CannotSkip
      end
  in
  let res = ref true in
  begin
    try
      checkKnownList [fname];
      Ftools.pf_s "FPAdebug" print_endline "CheckSkip: KnownList checking ... OK";
      (* checking whiteness of union X *)
      checkWhite_of_unionX sh fname;
      (* checking with history *)
      checkHistory sh fname eeArg;
    with
      CannotSkip -> res := false
  end;
  Ftools.pf_s "FPAdebug" print_endline "Skip check ends";
  !res

(*-----------------------------*)
(*  Function-Pointer Analysis  *)
(*-----------------------------*)
exception NOT_YET;;

(* "#abc_123" --> "abc" *)
let tempvar_original_name fp =
  match Bytes.get fp 0 with
  | '#' ->
     let len = Bytes.length fp in
     let _pos = ref (len-1) in (* !_pos points the position of the last '_' in fp *)
     begin            
       try
         for i = 0 to len - 1 do
           if Bytes.get fp (len - i - 1) = '_'
           then raise Exit
           else _pos := !_pos-1
         done;
       with
         Exit -> ();
     end;
     Bytes.sub fp 1 (!_pos - 1)
  | _ -> fp
;;

let rec tempvar_original_name_exp t =
  match t with
  | Kexp.Lval lval -> Kexp.Lval (tempvar_original_name_lval lval)
  | _ -> t
and tempvar_original_name_lval lval =
  match lval with
    | Kexp.Var (fp,tp) -> Kexp.Var (tempvar_original_name fp,tp)
    | _ -> lval

(* funcp for declarations *)
(* This has two modes: *)
(* (1) Modular-analysis mode: INPUT=(az,sh,Some fundata,decl,loc), OUTPUT=(sh,Some fundata)  *)
(* (2) Topdown-analysis mode: INPUT=(az,sh,None,decl,loc), OUTPUT=(sh,None)  *)
let funcp_decl loc decl (sh,prof_opt): FPsh.t * FunProfile.t option =
  let Kdecl.Decl (tpOut,lval,init) = Kdecl.shift_ptr_left decl in
  print_mes loc (Kdecl.to_string 0 decl);
  
  match lval,init with
  (* global function pointer without init --> make an entry *)    
  | Kexp.Var (fp,tp),Kinit.None when Kexp.isFpType tp && az.AZ.mode = AZ.GLOBAL ->
     print_mes loc "-- fp-decl: global function-pointer declaration";
     let (s,h) = sh in
     let s1: FPsh.store = FPsh.updateFP_s loc s fp [FPval.Fname []] in
     let sh1 = (s1,h) in
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     (sh1,prof_opt)
  (* Declarations without init --> do nothing *)
  | _,Kinit.None ->
     (sh,prof_opt)
    
  (* struct type variable with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructType tp) ->
     print_mes loc "-- fp-decl case-1";
     let preheap = allocTypeFP loc sh (tp,[-1]) init in
     let sh' = FPsh.update_by_preheap_sh sh preheap in
     (sh',prof_opt)
     
  (* struct type array with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructArrayType tp) ->
     print_mes loc "-- fp-decl case-2";
     let dim = Kexp.extract_dim' tp in
     let tp_iDim =
       try
         (fun (tp,ee) -> (tp,List.map (FPsh.evalCExpInt loc sh) ee)) dim
       with
         UNKNOWN -> (tp,[1]) (* dummy *)
     in
     let preheap = allocTypeFP loc sh tp_iDim init in
     let sh' = FPsh.update_by_preheap_sh sh preheap in
     (sh',prof_opt)
     
  (* simple type array with init --> do nothing *)
  | Kexp.Var (v,tp),_ when (Kexp.isSimpleArrayType tp) ->
     print_mes loc "-- fp-decl case-3.2 (do nothing)";
     (sh,prof_opt)

  (* function pointer with init *)
  | Kexp.Var (arr,tp),_ when Kexp.isFpType tp && Kexp.hasArray tp ->
     print_mes loc "-- fp-decl case-4.1a: function-pointer array case";
     let (s,h) = sh in
     let rec getExpL init =
       match init with
       | Kinit.S e -> [e]
       | Kinit.M initL -> unionL (List.map getExpL initL)
       | Kinit.None -> []
     in
     let ee = getExpL init in
     let fnameL = unionL (List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) ee) in
     let prof_opt1 = FunProfile.updateFn loc (unionL (List.map Kexp.getFunName ee)) prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 ee in
     (* let lval = Kexp.Ptr t in *)
     (* let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 lval in *)
     let (h1,_) = FPsh.updateUnionFpFlag_h loc h "*" "*" [FPval.Fname fnameL] in
     (*
     Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
     Ftools.pf_s "FPAdebug" (FPsh.println1_h h) "*";
     Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
     Ftools.pf_s "FPAdebug" (FPsh.println1_h h1) "*";
      *)
     let sh1 = (s,h1) in     
     (sh1,prof_opt2)
     
  (* function pointer with init *)
  | Kexp.Var (fp,tp),_ when Kexp.isFpType tp ->
     print_mes loc "-- fp-decl case-4.1b: function-pointer case";
     let (s,h) = sh in
     (* let fp' = tempvar_original_name fp in *)
     let rec getFuncL init =
       match init with
       | Kinit.S e ->
          FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh e
       | Kinit.M initL ->
          List.flatten (List.map getFuncL initL)
       | Kinit.None -> []
     in
     let s1: FPsh.store =
       let fnameL = getFuncL init in
       FPsh.updateFP_s loc s fp [FPval.Fname fnameL]
     in
     let sh1 = (s1,h) in
     let prof_opt1 =
       match prof_opt,init with
       | None,_ -> None
       | Some (fpr0,fpm0,fn0,ret0,fpoL0,fpposL0,history),Kinit.S exp when FunProfile.isFpHolder exp ->
          let fpr1 = exp :: fpr0 in
          let fpm1 = lval :: fpm0 in
          Some (fpr1,fpm1,fn0,ret0,fpoL0,fpposL0,history)
       | Some (fpr0,fpm0,fn0,ret0,fpoL0,fpposL0,history),Kinit.M [Kinit.S exp] when FunProfile.isFpHolder exp ->
          let fpr1 = exp :: fpr0 in
          let fpm1 = lval :: fpm0 in
          Some (fpr1,fpm1,fn0,ret0,fpoL0,fpposL0,history)
       | _,Kinit.S exp ->
          let prof_optA = FunProfile.updateFn loc (Kexp.getFunName exp) prof_opt in
          let prof_optB = FunProfile.updateFpr loc gi prof_optA [exp] in
          prof_optB
       | _,_ ->
          prof_opt
     in
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     (sh1,prof_opt1)

  (* Function prototype case --> do nothing (This case does not happen) *)
  | Kexp.Var (fname,tp),_ when Kexp.hasFunc tp ->
     print_mes loc "-- fp-decl case-4.2: function-prototype case (do nothing)";
     (sh,prof_opt)
     
  (* other cases --> do nothing *)
  | _,_ ->
     (sh,prof_opt)
;;               

(*
let minor = ref 0.0;;
 *)
module G  = Map.Make(String)
let saved_calls : bytes list G.t ref = ref G.empty;;

let makeDependencyList_fork fname =
  let loc = ("",0) in
  let deplistFile = gi.GI.slacDataDir ^ "/Fpa/deplist" in
  let mods = gi.GI.fmodules in
  let aux () = 
    let pid = Unix.fork () in
    match pid with
    | 0 -> (* child process *)
       begin
         try
           let knownlist = AZ.knownlist_flatten az in
           let knownlistSize = string_of_int (List.length knownlist) in
           print_mes ~opt:"ALWAYS" loc @@ "generating Deplist for " ^ fname ^ " (knownlist size: " ^ knownlistSize ^ ")";
           let deplist, calls = VcpAllC.get_dependency_set_of_list ~mods:mods !saved_calls fname knownlist in
           saved_calls := calls;
           Ftools.write_file deplistFile deplist;
           exit 0
         with
         | Sys_error mes -> failwith ("exception from child Sys_err " ^ mes)
         | _ -> failwith "exception from child"
       end
    | _ -> (* parent process *)
       begin
         try
           let (_,status) = Unix.wait () in
           match status with
           | Unix.WEXITED _ -> ()
           | _ -> 
              failwith "Exceptional case"
         with
         | _ ->
            failwith "deplist generating process was killed"
       end
  in
  aux ();
  let deplist : VcpAllC.rec_t list = Ftools.read_file deplistFile in
  deplist
;;

(*========================================*)
(* funcp for statement *)
(*========================================*)
(* Modular Analysis in a parameterized form *)
let modularAnalysis0 myFuncp_stmt_sh sp_tm fname =
  let loc = ("",0) in
  az.AZ.mode <- AZ.MOD;
  print_endline ("BEGIN: modular analysis for " ^ fname);
  let getFunBody_and_genShMod gi fname =
    match GI.getFundefBody gi fname with
    | None ->
       print_mes ~opt:"ALWAYS" ("",0) (fname ^ " is a missing function --> added to missing list and SKIP");
       az.AZ.missingFunlist <- Tools.union az.AZ.missingFunlist [fname];
       raise Skip
    | Some (tpRet,declPrms,stmtBody) ->
       (* tpVarL = [(tp0,fp0);(tp1,v1)(tp2,fp2)] *)
       let tpVarL = List.map (fun (Kdecl.Decl(tp,lval,_))->(tp,List.hd (Kexp.av_lval lval))) declPrms in
       (* tpVarIdxL = [ ((tp0,fp0),0); ((tp1,v1),1); ((tp2,fp2),2) ] *)
       let tpVarIdxL = putIndexes tpVarL in
       (* tpFpIdxL = [ ((tp0,fp0),0); ((tp2,fp2),2) ] *)
       let tpFpIdxL = List.filter (fun ((tp,_),_) -> Kexp.isFpType tp) tpVarIdxL in
       (* fpIdxL = [ (fp0,0); (fp2,2) ] *)
       let fpIdxL = List.map (fun ((_,v),idx) -> (v,idx)) tpFpIdxL in
       let sh0mod : FPsh.t = Ftools.read_file (gi.GI.slacDataDir ^ "/Fpa/fpaInitStoreHeapMod") in
       let fpValL = List.map (fun (fp,i)->(fp,[FPval.Ph ("$" ^ (string_of_int i))])) fpIdxL in
       (* sh1mod = sh0mod[fp0:=[0],fp2:=[2]] *)
       let sh1mod = FPsh.updateFP_many ("",0) sh0mod fpValL in
       (stmtBody,tpRet,sh1mod)
  in
  let myFuncpL recflag stmtBody_tpRetL funShModProfL =
    print_mes loc "myFuncpL starts";
    let _res = ref [] in
    for i = 0 to List.length stmtBody_tpRetL - 1 do
      let (stmt,tpRet) = List.nth stmtBody_tpRetL i in
      let (fname,shMod,profile) = List.nth funShModProfL i in
      (* aaa *)
      updateRetFunList gi.GI.slacDataDir recflag tpRet fname;
      (* aaa *)
      az.AZ.currentFunc <- fname;
      match List.mem fname az.AZ.funstack with
      | true ->
         print_mes loc ("No execution of funcp_stmt_sh for " ^ fname);
         _res := (fname,shMod,profile) :: !_res
      | false ->
         print_mes loc ("Entering " ^ fname ^ " (modular analysis)");
         az.AZ.currentFunc <- fname;
         az.AZ.funstack <- fname :: az.AZ.funstack;
         let shMod1 = FPsh.push shMod in
         match myFuncp_stmt_sh sp_tm stmt (shMod1,Some profile) with
         | (FPstate.SH sh1,Some profile1) ->
            az.AZ.funstack <- List.tl az.AZ.funstack;
            let sh2 = FPsh.closing sh1 in
            _res := (fname,sh2,profile1) :: !_res
         | (_,_) ->
            failwith ("modular analysis of " ^ fname ^ " was failed")
    done;
    List.rev !_res
  in
  let syntacticalAnalysis_and_save fnameL stmtBodyL funShModProfL =
    AZ.reset AZ.MODREC0 az;
    az.AZ.skipFunclist <- fnameL;    
    print_mes loc "myFuncpModRec0 starts";
    for i = 0 to List.length stmtBodyL - 1 do
      let stmt = List.nth stmtBodyL i in
      let (fname,shMod,profile) = List.nth funShModProfL i in
      print_mes loc ("Entering " ^ fname ^ " (modular analysis in ModRec0-mode)");
      az.AZ.currentFunc <- fname;
      az.AZ.funstack <- fname :: az.AZ.funstack;      
      match myFuncp_stmt_sh sp_tm stmt (shMod,Some profile) with
      | (FPstate.SH _,Some profile1) ->
         az.AZ.funstack <- List.tl az.AZ.funstack;         
         Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) profile1
      | (_,_) -> failwith ("modular analysis of " ^ fname ^ " was failed")
    done;
    for i = 0 to List.length stmtBodyL - 1 do
      let stmt = List.nth stmtBodyL i in
      let (fname,shMod,profile) = List.nth funShModProfL i in
      print_mes loc ("Entering " ^ fname ^ " (modular analysis in ModRec0-mode)");
      az.AZ.currentFunc <- fname;
      az.AZ.funstack <- fname :: az.AZ.funstack;
      match myFuncp_stmt_sh sp_tm stmt (shMod,Some profile) with
      | (FPstate.SH _,Some profile1) ->
         az.AZ.funstack <- List.tl az.AZ.funstack;
         Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) profile1
      | (_,_) -> failwith ("modular analysis of " ^ fname ^ " was failed")
    done;
    print_mes loc "myFuncpModRec0 ends"
  in
  let generate_ret_fpo_many shL fnameL profL =
    List.map (fun (sh,fname,prof) -> FunProfile.generate_ret_fpo sh fname prof) (zipLst3 shL fnameL profL)
  in
  let deplist = makeDependencyList_fork fname in
  (*
  let deplist = VcpAllC.get_dependency_set_of_list ~mods:gi.GI.fmodules fname knownlist in  
   *)
  print_mes loc "generating Deplist done\n";


  let analyzerFile = gi.GI.slacDataDir ^ "/Fpa/analyzer" in
  let aux dep =
    let pid = Unix.fork () in
    match pid with
    | 0 -> (* child process *)
       begin
         try
           match dep with
           | VcpAllC.NONREC fnameG ->
              (* Non-Recursive function case*)
              print_mes ~opt:"ALWAYS" ("",0) ("Modular Analysis of " ^ fnameG);
              let (stmtBody,tpRet,sh1mod) = getFunBody_and_genShMod gi fnameG in
              let prof0 = FunProfile.init () in
              AZ.reset AZ.MOD az;
              az.AZ.currentFunc <- fname;
              let (_,shA,profG0) = List.hd (myFuncpL false [(stmtBody,tpRet)] [(fnameG,sh1mod,prof0)]) in
              let profG1 = FunProfile.generate_ret_fpo shA fnameG profG0 in
              print_mes ~opt:"ALWAYS" ("",0) ("Modular Analysis of " ^ fnameG ^ " DONE");
              print_mes ~opt:"ALWAYS" ("",0) (fnameG ^ " is added to knownlist");
              az.AZ.knownList <- dep :: az.AZ.knownList;
              print_mes ~opt:"ALWAYS" loc ("Profile of " ^ fnameG ^ " is saved");
              Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fnameG) profG1;
              (* for Debugging *)         
              Ftools.pf_s "FPAdebug" print_endline "|||||||||||||||||||||||||||||||||||||||||||||||||||||||";
              Ftools.pf_s "FPAdebug" print_endline ("Modular analysis result for " ^ fnameG);
              (*
         Ftools.pf_s "FPAdebug" (fun sh -> print_string' "Init: "; FPsh.println sh) sh1mod;
         Ftools.pf_s "FPAdebug" (fun sh -> print_string' (fnameG ^ ": "); FPsh.println sh) shA;
         Ftools.pf_s "FPAdebug" print_string' "-----";
               *)
              Ftools.pf_s "FPAdebug" FunProfile.load_show [fnameG];
              Ftools.pf_s "FPAdebug" print_endline "|||||||||||||||||||||||||||||||||||||||||||||||||||||||";
              Ftools.write_file analyzerFile az;
              exit 0
              
           | VcpAllC.REC fnameL ->
              (* Recursive-function case: {F1,F2,F3} *)
              Ftools.pf_s "FPAdebug" print_endline "";
              let fnameSet = "{" ^ (string_of_list (fun x->x) "," fnameL) ^ "}" in
              print_mes ~opt:"ALWAYS" ("",0) ("Modular Analysis of " ^ fnameSet);
              Ftools.pf_s "FPAdebug" print_endline "Recursive function case";
              (* Create empty profile entries for fnameL *)
              List.iter
                (fun fname ->
                  Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) FunProfile.empty)
                fnameL;
              print_mes ~opt:"ALWAYS" ("",0) ("  " ^ fnameSet ^ " are added to knownlist");
              az.AZ.knownList <- dep :: az.AZ.knownList;
              (* stmtBodyShModL = [(P1,shMod1);(P2,shMod2);(P3,shMod3)] *)
              let stmtBodyShModL = List.map (getFunBody_and_genShMod gi) fnameL in
              let stmtBodyL = List.map fst3 stmtBodyShModL in
              let tpRetL = List.map snd3 stmtBodyShModL in
              let shModL = List.map thd3 stmtBodyShModL in
              (* funShModProfL = [(F1,shMod1,prof1);(F2,shMod2,prof2);(F3,shMod3,prof3)] *)
              let funShModProfL =
                List.map
                  (fun (fnameF,shModF) -> (fnameF,shModF,FunProfile.init ()))
                  (zipLst fnameL shModL)
              in
              (* Syntactical analysis and writing profiles of fnameL on disk *)
              print_mes ("",0) @@ "Syntactical Analysis of {" ^ (string_of_list (fun x->x) "," fnameL) ^ "} starts";
              Ftools.pf_s "FPAdebug" print_endline "Making FprFpmFn";
              syntacticalAnalysis_and_save fnameL stmtBodyL funShModProfL;
              print_mes ("",0) @@ "Syntactical Analysis of {" ^ (string_of_list (fun x->x) "," fnameL) ^ "} ends";
              (* DONE: Making+Saving FprFpmFn for fnameL *)
              
              (* Iteration *)
              let (shRecL,profRecL) =
                let rec aux (shL,profL) =
                  let funShProfL = zipLst3 fnameL shL profL in
                  AZ.reset AZ.MODREC az;
                  let funShProfL1 = myFuncpL true (zipLst stmtBodyL tpRetL) funShProfL in
                  let shL1 = List.map snd3 funShProfL1 in
                  let profL1 : FunProfile.t list = List.map thd3 funShProfL1 in
                  let nextProfL : FunProfile.t list = generate_ret_fpo_many shL1 fnameL profL1 in
                  List.iter (Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname)) nextProfL;
                  if FunProfile.getSizeL profL = FunProfile.getSizeL nextProfL
                  then (shL1,nextProfL)
                  else aux (shL1,nextProfL)
                in
                let profL = FunProfile.read_many fnameL in (* Reading the syntactical analysis results *)
                aux (shModL,profL)
              in
              let fnameProfL = zipLst fnameL profRecL in
              List.iter
                (fun (fname,prof) -> Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) prof)
                fnameProfL;
              print_mes ~opt:"ALWAYS" ("",0) ("Modular Analysis of " ^ fnameSet ^ " DONE");
              (* for Debugging *)
              Ftools.pf_s "FPAdebug" print_endline "|||||||||||||||||||||||||||||||||||||||||||||||||||||||";
              Ftools.pf_s "FPAdebug" print_endline "Modular analysis results";
              (*
              Ftools.pf_s "FPAdebug"
                (List.iter (fun (fname,sh) -> print_string' (fname ^ ": "); FPsh.println sh)) (zipLst fnameL shRecL);
               *)
              Ftools.pf_s "FPAdebug" print_string' "-----";
              Ftools.pf_s "FPAdebug" FunProfile.load_show fnameL;
              Ftools.pf_s "FPAdebug" print_endline "|||||||||||||||||||||||||||||||||||||||||||||||||||||||";
              Ftools.write_file analyzerFile az;
              exit 0
         with
           _ ->
           az.AZ.knownList <- dep :: az.AZ.knownList;
           Ftools.write_file analyzerFile az;
           exit 0
       end
    | _ -> (* parent process *)
       begin
         try
           let (_,status) = Unix.wait () in
           match status with
           | Unix.WEXITED _ ->
              let newAnalyzer : AZ.t = Ftools.read_file analyzerFile in
              az.AZ.knownList <- newAnalyzer.AZ.knownList;
              az.AZ.missingFunlist <- newAnalyzer.AZ.missingFunlist;
              az.AZ.fppos <- newAnalyzer.AZ.fppos;
              ()
           | _ -> 
              failwith "Exceptional case"
         with
         | _ ->
            failwith "deplist generating process was killed"
       end
  in
  let stack = ref (List.rev deplist) in
  while !stack <> [] do
    let dep = List.hd !stack in
    stack := List.tl !stack;
    try
      aux dep;
    with
    | Skip -> ()
  done;
  print_endline ("FINISH: modular analysis for " ^ fname);
  print_endline "";
  ()
;;


let rec funcp_stmt0 myModularAnalysis sp_tm stmt (r,prof_opt): FPstate.t * FunProfile.t option =
  match r with
  | FPstate.None -> (FPstate.None,prof_opt)
  | FPstate.SH sh -> funcp_stmt_sh0 myModularAnalysis sp_tm stmt (sh,prof_opt)
                   
and funcp_stmt_sh0 myModularAnalysis sp_tm stmt (sh,prof_opt) =
  (* let minor' = !minor in *)
  let (s,h) = sh in
  let strV = gi.GI.structs in
  let aliases = gi.GI.straliases in
  let funtable = gi.GI.funtable in
  let res =
  match stmt with
  | Kstmt.Decl (decl,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Decl";
     let (sh',prof_opt) = funcp_decl loc decl (sh,prof_opt) in
     let r' = FPstate.SH sh' in
     (r',prof_opt)
     
  | Kstmt.Skip -> (FPstate.SH sh,prof_opt)

  (* v = malloc(sizeof(tp)*t); *)
  | Kstmt.Malloc (v,tp,t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Malloc";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     let r' = FPstate.SH sh in
     (r',prof_opt)

  (* free(t); *)
  | Kstmt.Free (t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Free";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     let r' = FPstate.SH sh in
     (r',prof_opt)

  (* { P1;P2;P3 } *)
  | Kstmt.Block (stmtL,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Block";
     let _curdata = ref (FPstate.SH sh,prof_opt) in
     for i = 0 to List.length stmtL - 1 do
       _curdata := funcp_stmt0 myModularAnalysis sp_tm (List_mes.nth "funcp_stmt_sh:Block" stmtL i) !_curdata;
     done;
     !_curdata

     
  (* IF-THEN-statement *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) when Kstmt.isSkip stmtElse ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-If-Then";
     print_mes loc "IF-Then-statement";
     print_mes loc "Begin THEN";
     let (r',prof_opt1) = funcp_stmt_sh0 myModularAnalysis sp_tm stmtThen (sh,prof_opt) in
     print_mes loc "End THEN";
     (r',prof_opt1)
     
  (* IF-statement: SEQUENTIAL analysis *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-If-seq";
     print_mes loc "IF-statement";
     begin
       print_mes loc "Begin THEN";
       match funcp_stmt_sh0 myModularAnalysis sp_tm stmtThen (sh,prof_opt) with
       | (FPstate.None,prof_opt1) ->
          print_mes loc "End THEN";
          let r' = FPstate.SH sh in     
          (r',prof_opt1)
       | (FPstate.SH sh1,prof_opt1) ->
          print_mes loc "End THEN + Start ELSE";
          let (r',prof_opt2) = funcp_stmt_sh0 myModularAnalysis sp_tm stmtElse (sh1,prof_opt1) in
          print_mes loc "End ELSE";
          (r',prof_opt2)
     end
     
     (*
  (* IF-statement: NATURAL analysis *)

  | Kstmt.If (_,stmtThen,stmtElse,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-If-natural";
     print_mes loc "IF-statement";
     let (rThen,prof_opt1) = funcp_stmt_sh0 myModularAnalysis sp_tm stmtThen (sh,prof_opt) in
     let (rElse,prof_opt2) = funcp_stmt_sh0 myModularAnalysis sp_tm stmtElse (sh,prof_opt1) in
     let r' = FPstate.union loc rThen rElse in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     (r',prof_opt2)
      *)
     
  (* L:: *)
  | Kstmt.Lbl (_,_,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Label";
     let r' = FPstate.SH sh in
     (r',prof_opt)

  | Kstmt.Fail loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Fail";
     let r' = FPstate.SH sh in
     print_warn loc "fp encounters Fail";
     (r',prof_opt)
     
  | Kstmt.Break loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Break";
     let r' = FPstate.SH sh in
     print_warn loc "fp encounters Break (this should be eliminated by the prog.trans.)";
     (r',prof_opt)

  | Kstmt.Continue loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Continue";
     let r' = FPstate.SH sh in
     print_warn loc "fp encounters Continue (this should be eliminated by the prog.trans.)";
     (r',prof_opt)

  | Kstmt.Unknown loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Unknown";
     let r' = FPstate.SH sh in
     print_warn loc "fp: encounters Unknown";
     (r',prof_opt)
     
  (* return(t); *)
  | Kstmt.Return (e,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Return";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Return-case";     
     let r' = 
       match Kexp.getTrueType_opt strV aliases e with
       | Some tp when Kexp.isFpType tp ->
          let fnameL = FPsh.evalCExpFp_fnameL loc strV aliases funtable sh e in
          let s' = FPsh.updateRetUnionFP_s loc s fnameL in
          FPstate.SH (s',h)
       | _ ->
          FPstate.SH sh
     in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     (r',prof_opt)

  (* fp = t->fld *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),Kexp.Lval (Kexp.Arrow (u,tpStruct,fld)),loc) when Kexp.isFpType tp  ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(fp=t->fld)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (function-pointer: fp=t->f)-case";
     (* let fp' = tempvar_original_name fp in *)
     let strName =
       try
         Kexp.getStructName tpStruct (* This may return an exception (it is unexpected) *)
       with
         _ -> (print_endline "failed to get struct name"; failwith "")
     in
     let aliases = gi.GI.straliases in
     let value =
       match FPsh.lookup_h_field_fp loc aliases sh strName fld with
       | None ->
          failwith "Unexpected fp=t->fld"
       | Some value -> value
     in
     let updateFpFlagFun = FPsh.updateUnionFpFlag_s in
     let (s1,updateFlag) = updateFpFlagFun loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     AZ.update_whilestack az updateFlag;
     let r' = FPstate.SH (s1,h) in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" (fun _ -> FPsh.println_h_one strName (FPsh.lookup_h aliases sh strName)) ();
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     (* updating profile *)
     let lval = Kexp.Var (fp,tp) in
     let eFld = Kexp.Lval (Kexp.Arrow (u,tpStruct,fld)) in
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName eFld) prof_opt in     
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [eFld] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* fp = t *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),t,loc) when Kexp.isFpType tp  || Kexp.isFun t ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(fp=t)";
     print_mes loc (Kstmt.to_string "" 0 stmt);     
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (function-pointer: fp=t)-case";     
     let value = FPsh.evalCExpFp loc strV aliases funtable sh t in
     let updateFpFlagFun = FPsh.updateUnionFpFlag_s in
     let (s1,updateFlag) = updateFpFlagFun loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     let r' = FPstate.SH (s1,h) in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     (* updating profile *)
     let lval = Kexp.Var (fp,tp) in     
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName t) prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [t] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* x = t --> skip *)
  | Kstmt.Asgn (Kexp.Var (x,tp),t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(x=t)";
     print_mes loc (Kstmt.to_string "" 0 stmt);     
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     let r' = FPstate.SH (s,h) in
     (* updating profile *)
     let lval = Kexp.Var (x,tp) in     
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName t) prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [t] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* t<tp>->f = u; *)
  | Kstmt.Asgn (Kexp.Arrow (t,tp,fld),u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(t<tp>->f=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     let lval = Kexp.Arrow (t,tp,fld) in
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     (*
     (* for debugging --- *)
     if List.mem fld checkFldL
     then
       let fldValL = FPsh.lookup_h aliases sh strName in
       FPsh.print_h_one strName fldValL;
       print_endline "";
       failwith ""
     else ();
      *)
     begin       
       match Kexp.getTrueType_lval_opt gi.GI.structs aliases lval with
       | Some tp1 when Kexp.isFpType tp1 ->
          Ftools.pf_s "FPAfindbranch" print_endline "br-(t<tp>->f=u)-A";
          print_mes loc (Kstmt.to_string "" 0 stmt);
          (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
          print_mes loc "-- funcp_stmt: Asgn (t->f=u)-case";
          let strName = Kexp.getStructName tp in
          let value = FPsh.evalCExpFp loc strV aliases funtable sh u in
          let (sh1,updateFlag) = FPsh.updateUnionFpFlag_sh loc sh strName fld value in
          AZ.update_whilestack az updateFlag;
          let r' = FPstate.SH sh1 in
          Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
          Ftools.pf_s "FPAdebug" (FPsh.println_h_one strName) (FPsh.lookup_h aliases sh strName);
          Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
          Ftools.pf_s "FPAdebug" (FPsh.println_h_one strName) (FPsh.lookup_h aliases sh1 strName);
          (* updating profile *)
          let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in
          let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
          let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
          (r',prof_opt3)
       | _ ->
          Ftools.pf_s "FPAfindbranch" print_endline "br-(t<tp>->f=u)-B";          
          let r' = FPstate.SH (s,h) in
          (* updating profile *)
          let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in
          let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
          let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
          (r',prof_opt3)
     end

  (* *fp = u; *)
  | Kstmt.Asgn (Kexp.Ptr (Kexp.Lval (Kexp.Var(fp,tp))),u,loc) when Kexp.isFpType tp ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*fp=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (function-pointer2: *fp=u)-case";
     (*     let fp' = tempvar_original_name fp in  *)
     let value = FPsh.evalCExpFp loc strV aliases funtable sh u in
     let (s1,updateFlag) = FPsh.updateUnionFpFlag_s loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     let r' = FPstate.SH (s1,h) in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     (* updating profile *)
     let lval = Kexp.Ptr (Kexp.Lval (Kexp.Var(fp,tp))) in
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* *e = u; where e has a function pointer *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) when Kexp.hasFunPtrTp strV aliases t ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*fp=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (function-pointer2: *e=u with e:FP-type)-case";
     let value = FPsh.evalCExpFp loc strV aliases funtable sh u in
     let (h1,updateFlag) = FPsh.updateUnionFpFlag_h loc h "*" "*" value in (* h1 = h[("*","*"):=h("*","*")+fnameL] *)
     let r' = FPstate.SH (s,h1) in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     (*
     Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
     Ftools.pf_s "FPAdebug" (FPsh.println1_h h) "";
     Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
     Ftools.pf_s "FPAdebug" (FPsh.println1_h h1) "";
      *)
     (* updating profile *)
     let lval = Kexp.Ptr t in
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)
     
  (* *t = u; --> do nothing *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*t=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);     
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn [*t=u]-case";
     let r' = FPstate.SH sh in
     (* updating profile *)
     let lval = Kexp.Ptr t in
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in     
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* arr[t1][t2] = u; --> do nothing since this form would not come *)
  | Kstmt.Asgn (Kexp.Array (aLval,tt),u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Array-assign";
     print_mes loc (Kstmt.to_string "" 0 stmt);          
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (arr[t]=u)-case";
     let r' = FPstate.SH sh in
     (* updating profile *)
     let lval = Kexp.Array (aLval,tt) in
     let prof_opt1 = FunProfile.updateFn loc (Kexp.getFunName u) prof_opt in     
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 [u] in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 [lval] in
     (r',prof_opt3)

  (* while(b) P; (fixed-point-computation) *)
  | Kstmt.While (_,_,stmtBody,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-19";
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "WHILE-statement";
     let _curdata = ref (FPstate.SH sh,prof_opt) in
     begin
       try
         while true do
           AZ.push_whilestack az;
           _curdata := funcp_stmt0 myModularAnalysis sp_tm stmtBody !_curdata;
           if not (AZ.pop_whilestack az) then raise Exit else ();
         done;
       with
         _ -> ()
     end;
     !_curdata

  (* Missing functions *)
  | Kstmt.Fcall (fname,_,_,_,loc) when List.mem fname az.AZ.missingFunlist ->
     print_mes loc (fname ^ " is a missing function --> Skip");
     let r = FPstate.SH (s,h) in
     (r,prof_opt)
     
  (* Special handling functions *)
  | Kstmt.Fcall (fname,tt,_,_,loc) when isDebugFun(fname) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-SP-FunCall";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     begin       
       match fname with (* special handling for debugging purpose *)
       | "__EVAL" ->
          for i = 0 to List.length tt - 1 do
            let fp = Kexp.getVarName (List_mes.nth "funcp_stmt_sh:FCall" tt i) in
            let fnameL = FPsh.evalFP loc sh fp in
            print_string' @@ "__EVAL: s(" ^ fp ^ ")={";
            print_list print_string' "," fnameL;
            print_string' @@ "}";
          done;
       | "__COMMENT" ->
          let v = Kexp.getVarName (List_mes.hd "cc" tt) in
          print_mes loc @@ "__COMMENT: " ^ v
       | "__SHOW" ->
          print_mes loc @@ "__SHOW";
          Kstmt.println stmt;
       | "__QUIT" ->
          print_mes loc @@ "__QUIT";
          exit 0;
       | _ -> ()
     end;
     let r = FPstate.SH (s,h) in
     (r,prof_opt)

  (* (fp)(t1,..,tn) / (#f)(t1,..,tn) (SECOND stage) *)
  | Kstmt.FPcall (fp,pos,tt,tpRet,tpPrm,loc)
       when List.mem az.AZ.mode [AZ.MOD;AZ.MODREC;AZ.MODREC0] && az.AZ.nth > 1 ->
     print_mes loc ("FPCALL (MOD/MODREC): " ^ (Kstmt.to_string "" 0 stmt));
     print_mes loc (Kstmt.to_string "" 0 stmt);
     print_mes loc "Function Pointer Call in MOD-mode";
     let curFunc = az.AZ.currentFunc in
     let fp' = tempvar_original_name fp in
     let value1 = 
       match FPsh.evalFP_s_opt loc s fp, FpPos.eval az.AZ.fppos (curFunc,fp,pos) with
       | None, value0 -> value0
       | Some value, value0 -> FPval.union value value0
     in
     (* update FpPos *)
     azUpdateFppos loc curFunc fp' pos value1;
     (* updating Profile *)
     let fpHolder = Kexp.Lval (Kexp.Var (fp,[Kexp.FUNCPTR(tpRet,tpPrm); Kexp.OTHER "GLOBAL"])) in
     let prof_opt1 = FunProfile.updateFpr loc gi prof_opt (fpHolder :: tt) in
     (* analysis of FPcalled functions *)
     let (fnameL,_,_) = FPval.split value1 in
     let r = FPstate.SH (s,h) in
     let (r,prof_opt2) =
       List.fold_left
         (fun r_profOpt f ->
           print_mes loc (f ^ " is analyzed by FPcall");
           let stmt1 = Kstmt.Fcall (f,tt,tpRet,tpPrm,loc) in
           try
             funcp_stmt0 myModularAnalysis sp_tm stmt1 r_profOpt
           with
             _ -> (print_endline ("SOMETHING HAPPENS IN " ^ f); r_profOpt)
         )
         (r,prof_opt1)
         fnameL
     in
     (r,prof_opt2)
     
  (* (fp)(t1,..,tn) / (#f)(t1,..,tn) *)
  | Kstmt.FPcall (fp,pos,tt,tpRet,tpPrm,loc) when List.mem az.AZ.mode [AZ.MOD;AZ.MODREC;AZ.MODREC0] ->
     print_mes loc ("FPCALL (MOD/MODREC): " ^ (Kstmt.to_string "" 0 stmt));
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "Function Pointer Call in MOD-mode --> skip";
     let curFunc = az.AZ.currentFunc in
     let fp' = tempvar_original_name fp in
     let value1 = 
       match FPsh.evalFP_s_opt loc s fp, AZ.evalFppos az curFunc fp pos with
       | None, value0 -> value0
       | Some value, value0 ->
          let value1 = FPval.union value value0 in
          value1
     in
     (* update FpPos *)
     azUpdateFppos loc curFunc fp' pos value1;
     (* updating Profile *)
     let fpHolder = Kexp.Lval (Kexp.Var (fp,[Kexp.FUNCPTR(tpRet,tpPrm); Kexp.OTHER "GLOBAL"])) in
     let prof_opt1 = FunProfile.updateFpr loc gi prof_opt (fpHolder :: tt) in
     let prof_opt2 = FunProfile.updateFppos loc gi prof_opt1 curFunc fp' pos value1 in
     let r = FPstate.SH (s,h) in     
     (r,prof_opt2)
     
  (* (fp)(t1,..,tn) / (#f)(t1,..,tn) : execute FPcall (in FPA-mode) *)
  | Kstmt.FPcall (fp,pos,tt,tpRet,tpPrm,loc) ->
     print_mes loc ("FPCALL (FPA): " ^ (Kstmt.to_string "" 0 stmt));
     print_mes loc (Kstmt.to_string "" 0 stmt);          
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "Function Pointer Call in FPA-mode";
     let curFunc = az.AZ.currentFunc in     
     let fp' = tempvar_original_name fp in
     begin
       match FPsh.evalFP loc sh fp with (* s(fp) *)
       | [] ->
          C.print_warn loc @@ "FpCall: " ^ fp ^ " is empty!! (skip)";
          azUpdateFppos loc curFunc fp' pos FPval.none;
          (* updating Profile *)
          let fpHolder = Kexp.Lval (Kexp.Var (fp,[Kexp.FUNCPTR(tpRet,tpPrm)])) in
          let prof_opt1 = FunProfile.updateFpr loc gi prof_opt (fpHolder :: tt) in
          let prof_opt2 = FunProfile.updateFppos loc gi prof_opt1 curFunc fp' pos [FPval.Fname []] in
          let r = FPstate.SH (s,h) in
          (r,prof_opt2)
       | fnameL ->
          print_mes loc @@ "FpCall: " ^ fp ^ "!" ^ (string_of_int pos) ^ " in " ^ curFunc;
          (* print fppos-1 *)
          Ftools.pf_s "FPAdebug" print_string' "-- PRE (az.fppos): ";
          Ftools.pf_s "FPAdebug" azShowFppos_filter (curFunc,fp,pos);
          (* print fppos-1 *)          
          let value0 = AZ.evalFppos az curFunc fp pos in
          let (fnameL1,_,_) = FPval.split value0 in
          let fnameL2 = union fnameL fnameL1 in (* New data of s(F,fp,pos) *)
          azUpdateFppos loc curFunc fp' pos [FPval.Fname fnameL2];
          (* print fppos-2 *)          
          Ftools.pf_s "FPAdebug" print_string' "-- POST (az.fppos): ";
          Ftools.pf_s "FPAdebug" azShowFppos_filter (curFunc,fp,pos);
          (* print fppos-2 *)          
          (* updating Profile *)
          let fpHolder = Kexp.Lval (Kexp.Var (fp,[Kexp.FUNCPTR(tpRet,tpPrm)])) in
          let prof_opt1 = FunProfile.updateFpr loc gi prof_opt (fpHolder :: tt) in
          let prof_opt2 = FunProfile.updateFppos loc gi prof_opt1 curFunc fp' pos [FPval.Fname fnameL2] in
          let (r,prof_opt3) =
            List.fold_left
              (fun r_profOpt fname ->
                print_mes loc ("--> " ^ fp ^ " is replaced by " ^ fname);
                let stmt1 = Kstmt.Fcall (fname,tt,tpRet,tpPrm,loc) in
                funcp_stmt0 myModularAnalysis sp_tm stmt1 r_profOpt
              )
              (FPstate.SH sh,prof_opt2)
              fnameL2
          in
          (r,prof_opt3)
     end

  (* F(t1,..,tn) / F(t1,..,tn) (MODREC0-mode) *)
  | Kstmt.Fcall (fname,eeArg,tpRet,_,loc) when (az.AZ.mode = AZ.MODREC0) ->
     (* updating Profile *)
     let (fpr,fpm,fn,_,_,_,_) = FunProfile.get fname in
     let prof_opt1 = FunProfile.updateFn loc fn prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 fpr in
     let prof_opt3 = FunProfile.updateFpm loc gi prof_opt2 fpm in
     let r = FPstate.SH sh in
     (r,prof_opt3)
     
  (* F(t1,..,tn) / F(t1,..,tn) (SKIP CASE) *)
  | Kstmt.Fcall (fname,eeArg,_,_,loc)
       when az.AZ.noMod = false && skipCheck myModularAnalysis sp_tm loc sh eeArg fname ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-FCall-Skip";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     print_mes loc @@ "Skip checking result: True --> Skipped";
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     (* get profile of fname *)
     let (fpr,fpm,_,retVal,fpoL,fpposL,_) = FunProfile.get fname in     
     (* making sigma *)
     let sigma1 : (bytes * FPval.t) list =
       let numL = List.rev (genLst (List.length eeArg)) in
       List.fold_left
         (fun sigma (n,e) ->
           let nVar = "$" ^ (string_of_int n) in
           let eVal = FPsh.evalCExpFp loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh e in
           (nVar,eVal) :: sigma
         )
         []
         (zipLst numL eeArg)
     in
     let sigma2 : (bytes * FPval.t) list =
       List.fold_left
         (fun s e -> 
           let eVal = FPsh.evalCExpFp loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh e in
           let eName = FPval.toBarVarName (Kexp.getFpHolderName gi.GI.straliases e) in
           (eName,eVal) :: s)
         []
         fpr
     in
     let sub = sigma1 @ sigma2 in
     (* substitution for retVal *)     
     let retVal1 = FPval.subst sub retVal in
     (* substitution for fpoL *)
     let fpoL1 = FunProfile.subst_fpoL sub fpoL in
     (* making substitution of fpoL *)     
     let sub_fpoL =
       List.fold_left
         (fun sub (e,value) ->
           match e with
           | Kexp.Var (v,_) -> (v,value) :: sub
           | _ -> sub)
         []
         fpoL1
     in
     (*
     (* making substitution of fpposL *)     
     let sub_fpposL =
       List.fold_left
         (fun sub (fname1,fp1,n1,value1) ->
           match value with
           | FPval.Fname _ when fname1 = fname -> (fname1,fp1,n1,value1) :: sub
           | _ -> sub)
         []
         fpposL
     in
      *)
     (* making new sh and the output *)
     let sh1 = FPsh.updateRetVal loc sh retVal1 in
     let sh2 = FPsh.updateFP_many loc sh1 sub_fpoL in
     let r = FPstate.SH sh2 in
     (* updating fppos *)
     if fpposL = [] then ()
     else
       begin
         let fpposL' = FunProfile.subst_fpposL sub fpposL in
         Ftools.pf_s "FPAdebug" print_endline "UUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUU";
         Ftools.pf_s "FPAdebug" print_endline ("Updating fppos of " ^ fname ^ (if az.AZ.mode = AZ.FPA then " (FPA)" else " (MOD)"));
         Ftools.pf_s "FPAdebug" FPsh.println_s (fst sh2);
         Ftools.pf_s "FPAdebug" print_endline @@ "UUUUUUUUUU";     
         Ftools.pf_s "FPAdebug" FunProfile.print_fpposL fpposL';
         Ftools.pf_s "FPAdebug" print_endline "UUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUU";
         azUpdateFppos_many loc fpposL';
       end;
     (* updating Profile *)
     let fnameL = Kexp.getFunNameL eeArg in
     let prof_opt1 = FunProfile.updateFn loc fnameL prof_opt in
     let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 eeArg in
     (r,prof_opt2)

  (* F(t1,..,tn) / F(t1,..,tn) (NORMAL CASE) *)
  | Kstmt.Fcall (fname,eeArg,tpRet,_,loc) ->
     (*     let tm1 = Sys.time () in     *)
     Ftools.pf_s "FPAfindbranch" print_endline "br-FCall-NotSkip";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     (* update history in the MOD-mode *)
     let prof_opt_his =
       let prof_opt_old = Some (FunProfile.get fname) in
       if List.mem az.AZ.mode [AZ.MOD;AZ.MODREC]
       then
         begin
           let prof_opt_new = FunProfile.updateHistory_save loc fname sh eeArg prof_opt_old in
           print_mes loc ("Updating history for " ^ fname);
           Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
           Ftools.pf_s "FPAdebug" print_endline ("@@@ Previous Profile of " ^ fname);
           Ftools.pf_s "FPAdebug" FunProfile.println_opt prof_opt_old;
           Ftools.pf_s "FPAdebug" print_endline ("@@@ Updated Profile of " ^ fname);
           Ftools.pf_s "FPAdebug" FunProfile.println_opt prof_opt_new;
           Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
           prof_opt_new
         end
       else prof_opt_old
     in
     let tm1 = Sys.time () in
     match GI.getFundefBody gi fname with
     | None ->
        (* No-definition case -> do nothing *)
        C.print_warn loc @@ fname ^ " : definition NotFound --> Empty profile is created + added to KnownList";
        az.AZ.knownList <- (VcpAllC.NONREC fname) :: az.AZ.knownList;
        az.AZ.missingFunlist <- Tools.union az.AZ.missingFunlist [fname];
        Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) FunProfile.empty;
        let r = FPstate.SH (s,h) in
        (* updating the current profile *)
        let fnameL = Kexp.getFunNameL eeArg in
        let prof_opt1 = FunProfile.updateFn loc fnameL prof_opt_his in
        let prof_opt2 = FunProfile.updateFpr loc gi prof_opt1 eeArg in
        (r,prof_opt2)
     | Some (tpRet,declPrms,stmtBody) ->
        print_mes loc ("Entering " ^ fname);
        
        (* Pre-processing *)
        Ftools.pf_s "FPAdebug" (AZ.add_show_funstack fname) az;
        print_mes loc (fname ^ " is added to funstack");
        az.AZ.funstack <- fname :: az.AZ.funstack;
        az.AZ.currentFunc <- fname;
        let sh1 = FPsh.push sh in
        (*
        let (tpRet0,tpParam0) = Kexp.getFunctionTp tpRet in
         *)
        (* If fname is the checking function, then the "-deb FPAcheck" flag is turned on *)
        Ftools.pf_s fname (fun _ ->
            print_endline @@ "VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV";
            print_endline @@ "Begin Detailed Checking Mode: ";
            print_endline @@ "FUNCNAME: " ^ fname;
            print_endline @@ "-------------------------------------------------------------";
            Ftools.p_opt := "FPAcheck" :: !Ftools.p_opt;
          ) ();
        (* Showing argument info *)
        Ftools.pf_s "FPAcheck" print_endline "= PARAM;ARGUMENT;VALUE ====";
        Ftools.pf_s "FPAcheck"
          (List.iter (fun (prm,tArg) ->
               print_string' @@ (Kdecl.to_string 0 prm);
               print_string' @@ (Kexp.to_string tArg) ^ "; ";
               if Kexp.isFpType (Kdecl.getTp prm)
               then
                 begin
                   print_string' "{";
                   FPval.print (FPsh.evalCExpFp loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh1 tArg);
                   print_string' "}\n"
                 end
               else
                 print_endline "None";
             )
          )
          (zipLst declPrms eeArg);
        Ftools.pf_s "FPAcheck" print_endline "===========================";
        (* Renaming all local variables *)
        let localVarL = unionL ((Kstmt.dv stmtBody) :: (List.map Kdecl.dv declPrms)) in
        let rename =
          List.map
            (fun v ->
              let v' = "#" ^ v ^ "_" ^ (string_of_int az.AZ.localVarCtr) in
              AZ.inclLocalVarCtr az;
              (v,v')
            )
            localVarL
        in
        let declPrms0 = List.map (Kdecl.simple_renaming rename) declPrms in
        let stmtBody0 = Kstmt.simple_renaming rename stmtBody in
        let declPrms' = List.map Kdecl.shift_ptr_left declPrms0 in
        let prm_arg = List.map (fun (Kdecl.Decl (tp,lval,_),e) -> (tp,lval,e)) (zipLst declPrms' eeArg) in (* [(int,x1,t1);(int*,x2,t2)] *)
        let (prmPtrL,prmNPtrL) = List.partition (fun (tp,_,_) -> Kexp.isPtrType tp) prm_arg in (* ( [(int*,x2,t2)],[(int,x1,t1)] ) *)
        (*******)
        (* about non-pointers *)
        let stmtDeclL = 
          List.map
            (fun (tp,lval,t) -> Kstmt.Decl (Kdecl.Decl (tp,lval,Kinit.S t),loc))
            prmNPtrL
        in 
        let stmtBodyL = Kstmt.unBlock stmtBody0 in
        let stmtBodyL1 = stmtDeclL @ stmtBodyL in (* int x1=t1; body*)
        let stmtBody1 = Kstmt.mkBlock stmtBodyL1 loc in
        (* about pointers (substitution P[p:=&t] + program transformation: *&t -> t) *)
        let substPtr =
          List.flatten
            (List.map
               (fun (tp,lval,t) ->
                 match lval,t with
                 | Kexp.Var (v,_), Kexp.Lval (Kexp.Var(fname,tpA)) when Kexp.isFunType tpA ->
                    let t' = (Kexp.Addr (Kexp.Var(fname,tpA))) in
                    [(v,t')]
                 | Kexp.Var (v,_),_ -> [(v,t)]
                 | Kexp.Arrow _,_ -> []
                 | Kexp.Ptr _,_ -> []
                 | Kexp.Array _,_ -> []
               )
               prmPtrL)
        in
        let stmtBody2 = Kstmt.subst_elim_AstAnd_toplevel substPtr stmtBody1 in
        (******)
        Ftools.pf_s "FPAdebug" print_endline "--- Modified function body";
        Ftools.pf_s "FPAdebug" Kstmt.println stmtBody2;
        Ftools.pf_s "FPAdebug" print_endline "---";
        (* Main: Do funcp for the body *)       
        let (r2,prof_opt2) = funcp_stmt_sh0 myModularAnalysis sp_tm stmtBody2 (sh1,prof_opt_his) in
        let tm2 = Sys.time () in
        C.print_mes loc @@ "Leaving " ^ fname ^ " (time: " ^ (string_of_float (tm2-.tm1)) ^ ")";
        (* Post-processing *)
        let sh2a =
          match r2 with
          | FPstate.None -> sh
          | FPstate.SH sh' -> FPsh.closing sh'
        in
        print_mes loc @@ fname ^ " is removed from funstack";
        az.AZ.funstack <- List.tl az.AZ.funstack;
        az.AZ.currentFunc <- if az.AZ.funstack = [] then "" else List.hd (az.AZ.funstack);
        (* If fname is the checking function, then the "-deb FPAcheck" flag is turned off *)
        Ftools.pf_s fname (fun _ ->
            print_endline @@ "-------------------------------------------------------------";
            print_endline @@ "End Detailed Checking Mode: " ^ fname;
            print_endline @@ "VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV";
            Ftools.p_opt := List.tl !Ftools.p_opt) ();
        let r' = FPstate.SH sh2a in
        (* updating Profile *)
        let fnameL = Kexp.getFunNameL eeArg in
        let prof_opt3 = FunProfile.updateFn loc fnameL prof_opt2 in
        let prof_opt4 = FunProfile.updateFpr loc gi prof_opt3 eeArg in
        (r',prof_opt4)
  in
  (* let _ = sz_sh (fst res) in *)
  (* prerr_string "DBG:: "; Kstmt.println stmt;
  let mn = Gc.minor_words () in
  prerr_endline ("DBG:: " ^ (string_of_float (mn -. minor')));
  minor := mn;
  (FPstate.SH sh, ret) *)
  res
;;         


(* Toplevel of Modular Analysis and Funcp*)
let rec modularAnalysis sp_tm fname =
  modularAnalysis0 funcp_stmt_sh sp_tm fname
and funcp_stmt sp_tm stmt (r,prof_opt) : FPstate.t * FunProfile.t option =
  funcp_stmt0 modularAnalysis sp_tm stmt (r,prof_opt) 
and funcp_stmt_sh sp_tm stmt (r,prof_opt) =
  funcp_stmt_sh0 modularAnalysis sp_tm stmt (r,prof_opt)
;;



let initialization () : GI.t * FPstate.t =
  let gi = GI.init () in
  let s0 = FPsh.s_init [] "" in
  let h0 = FPsh.h_empty in
  let r0 = FPstate.SH (s0,h0) in
  (gi, r0)
;;
    
(* type of saving data: (shFp,shMod,structV,structAliasV,funtableV) *)
type kdata = FPsh.t * GI.structInfo * GI.strAliases * GI.funTable
;;

(* Pre-analysis *)
let preAnalyze_a_module kmodule mod_id : kdata =
  let sp_tm = Spacetime.Series.create "~/spacetime-sp" in
  let (mod_name,path,structV,straliasV,prog) = kmodule in
  (* creating & initializing an analyzer *)
  GI.reset gi;
  AZ.reset AZ.GLOBAL az;
  let sh0 = (FPsh.s_init [] "",FPsh.h_empty) in
  let r0 = FPstate.SH sh0 in
  gi.GI.structs <- V.fold (fun sName s m -> V.add sName s m) V.empty structV;
  gi.GI.straliases <- straliasV;
  (* creating initial states *)  
  let _curdata = ref (r0,None) in
  for j = 0 to List.length prog - 1 do
      let topdecl = List_mes.nth "preAnalyze_a_module" prog j in
      match topdecl with
      | KtopDecl.NA loc -> ()
      | KtopDecl.S (stmt,loc) ->
         (* Kstmt.println stmt; *)
         (* print_string' ".";  *)
         _curdata := funcp_stmt sp_tm stmt !_curdata (* execute funcp in the topdown-mode*)
      | KtopDecl.F (tp,fname1,_,_,loc) ->
         (* print_endline @@ "Processing Func.decl: " ^ fname1; *)
         (* print_endline @@ Klocs.to_string loc; *)
         (* print_string' ","; *)
         gi.GI.funtable <- V.add fname1 (mod_name,mod_id,j) gi.GI.funtable
  done;
  Ftools.dbg "GC" "After FPA main:" Ftools.print_gc (Gc.stat ());
  let sh = 
    match !_curdata with
    | (FPstate.SH sh,_) -> sh
    | (FPstate.None,_) -> FPsh.sh_init [] ""
  in
  (sh,gi.GI.structs,gi.GI.straliases,gi.GI.funtable)
;;


(* The main routine of FPA *)
let mainAnalysis_mod slacDataDir fname sp_tm =
  (* Path setting *)
  let fpaInitStoreHeapFp = slacDataDir ^ "/Fpa/fpaInitStoreHeapFp" in
  let fpaStructures = slacDataDir ^ "/Fpa/fpaStructures" in
  let fpaStructAliases = slacDataDir ^ "/Fpa/fpaStructAliases" in
  let fpaFuntable = slacDataDir ^ "/Fpa/fpaFuntable" in
  let fpaFundef = slacDataDir ^ "/Fpa/Fundef" in
  let fpaProfiles = slacDataDir ^ "/Fpa/Profiles" in
  let fpaFpPos = slacDataDir ^ "/Fpa/fppos" in
  let fpaState = slacDataDir ^ "/Fpa/state" in
  
  (* Initialization of GlobalInfo *)
  GI.reset gi;
  let structInfo : GI.structInfo = Ftools.read_file fpaStructures in
  let aliases: GI.strAliases = Ftools.read_file fpaStructAliases in
  let funtable : GI.funTable = Ftools.read_file fpaFuntable in
  let fmods : (int * VcpAllC.t) list = Ftools.read_allfiles (slacDataDir ^ "/Translated") in
  let fmoduleL = List.map snd fmods in
        
  gi.GI.structs <- structInfo;
  gi.GI.straliases <- aliases;
  gi.GI.funtable <- funtable;
  gi.GI.slacDataDir <- slacDataDir;
  gi.GI.fundefdir <- fpaFundef;
  gi.GI.fpaFunProfileDir <- fpaProfiles;
  gi.GI.fmodules <- fmoduleL;
  
  (* Initalized sh *)  
  let sh0Fp = Ftools.read_file fpaInitStoreHeapFp in

  let (modulename,fundef) : bytes * KtopDecl.t =
    let (_,mod_id,pos) =
      try
        V.find fname gi.GI.funtable
      with
        Not_found ->
        failwith ("List.assoc-3: Missing function > " ^ fname)
    in
    GI.lookup_fundef gi (mod_id,pos)
  in

  let toplevelanalysis nth (fppos0 : FpPos.t) = 
    (* Modular Analysis *)
    az.AZ.nth <- nth;
    print_mes ~opt:"ALWAYS" ("",0) ("Modular Analysis of " ^ fname ^ "@" ^ modulename);    
    modularAnalysis sp_tm fname;
    (* Main Analysis *)
    print_mes ~opt:"ALWAYS" ("",0) ("Main-analysis of " ^ fname ^ " begins");
    AZ.reset AZ.FPA az;
    az.AZ.currentFunc <- fname;
    az.AZ.funstack <- [fname];
    let (prms,loc,stmtBody) =
      match fundef with
      | KtopDecl.F (tp,_,prms,stmtBody,loc) -> (prms,loc,stmtBody)
      | _ -> failwith @@ "[E FPA] No function definition of " ^ fname
    in
    let stmtHeadL = List.map (fun decl -> Kstmt.Decl (decl,loc)) prms in
    let loc1 = Kstmt.getloc stmtBody in
    let stmtBodyL = Kstmt.unBlock stmtBody in
    let stmtStart = Kstmt.Block (stmtHeadL @ stmtBodyL,loc1) in
    let (r1,_) = funcp_stmt_sh sp_tm stmtStart (sh0Fp,None) in
    let fppos = az.AZ.fppos in
    let fppos1 = FpPos.subst aliases r1 fppos in
    let fppos2 = FpPos.finalize fppos1 in
    (r1,fppos2)
  in
  begin
    match az.AZ.twice with
    | true ->
       begin     
         let pid = Unix.fork () in
         match pid with
         | 0 -> (* child process *)
            begin          
              print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
              print_endline "FIRST STAGE ";
              print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
              try
                let (_,fppos) = toplevelanalysis 1 FpPos.empty in
                Ftools.write_file fpaFpPos fppos;
                exit 0
              with
              | _ ->
                 print_endline "SOMETHING HAPPENS";
                 exit 0
            end
         | _ -> (* parent process *)
            begin         
              try
                let (_,status) = Unix.wait () in
                print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
                print_endline "SECOND STAGE ";
                print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
                match status with
                | Unix.WEXITED _ ->
                   let fppos : FpPos.t = Ftools.read_file fpaFpPos in 
                   let (r',fppos') = toplevelanalysis 2 fppos in
                   az.AZ.fppos <- fppos';
                   Ftools.write_file fpaState r'
                | _ -> 
                   failwith "Exceptional case"
              with
              | _ ->
                 failwith "second stage was killed"
            end
       end
    | false ->
       print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
       print_endline "One Time execution";
       print_endline "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
       let (r',fppos') = toplevelanalysis 1 FpPos.empty in
       az.AZ.fppos <- fppos';
       Ftools.write_file fpaState r'
  end;
  let r1 : FPstate.t = Ftools.read_file fpaState in
  let fppos' = az.AZ.fppos in
  print_endline "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  FpPos.println fppos';    
  print_endline "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  
  (r1,fppos')
;;

(* Non-modular analysis *)
let mainAnalysis_noMod slacDataDir fname sp_tm =
  (* Path setting *)
  let fpaInitStoreHeapFp = slacDataDir ^ "/Fpa/fpaInitStoreHeapFp" in
  let fpaStructures = slacDataDir ^ "/Fpa/fpaStructures" in
  let fpaStructAliases = slacDataDir ^ "/Fpa/fpaStructAliases" in
  let fpaFuntable = slacDataDir ^ "/Fpa/fpaFuntable" in
  let fpaFundef = slacDataDir ^ "/Fpa/Fundef" in
  let fpaProfiles = slacDataDir ^ "/Fpa/Profiles" in
  
  (* Initialization of GlobalInfo *)
  GI.reset gi;
  let structInfo : GI.structInfo = Ftools.read_file fpaStructures in
  let aliases: GI.strAliases = Ftools.read_file fpaStructAliases in
  let funtable : GI.funTable = Ftools.read_file fpaFuntable in
  let fmods : (int * VcpAllC.t) list = Ftools.read_allfiles (slacDataDir ^ "/Translated") in
  let fmoduleL = List.map snd fmods in
        
  gi.GI.structs <- structInfo;
  gi.GI.straliases <- aliases;
  gi.GI.funtable <- funtable;
  gi.GI.slacDataDir <- slacDataDir;
  gi.GI.fundefdir <- fpaFundef;
  gi.GI.fpaFunProfileDir <- fpaProfiles;
  gi.GI.fmodules <- fmoduleL;

  (* Initalized sh *)  
  let sh0Fp = Ftools.read_file fpaInitStoreHeapFp in

  let (modulename,fundef) : bytes * KtopDecl.t =
    let (_,mod_id,pos) =
      try
        V.find fname gi.GI.funtable
      with
        Not_found ->
        failwith ("List.assoc-3: Missing function > " ^ fname)
    in
    GI.lookup_fundef gi (mod_id,pos)
  in

  AZ.reset AZ.FPA az;
  az.AZ.currentFunc <- fname;
  az.AZ.funstack <- [fname];
  az.AZ.nth <- 1;
  print_mes ~opt:"ALWAYS" ("",0) ("Non-Modular Analysis of " ^ fname ^ "@" ^ modulename);  
  let (prms,loc,stmtBody) =
    match fundef with
    | KtopDecl.F (tp,_,prms,stmtBody,loc) -> (prms,loc,stmtBody)
    | _ -> failwith @@ "[E FPA] No function definition of " ^ fname
  in
  let stmtHeadL = List.map (fun decl -> Kstmt.Decl (decl,loc)) prms in
  let loc1 = Kstmt.getloc stmtBody in
  let stmtBodyL = Kstmt.unBlock stmtBody in
  let stmtStart = Kstmt.Block (stmtHeadL @ stmtBodyL,loc1) in
  let (r1,_) = funcp_stmt_sh sp_tm stmtStart (sh0Fp,None) in
  let fppos = az.AZ.fppos in
  let fppos1 = FpPos.subst aliases r1 fppos in
  let fppos2 = FpPos.finalize fppos1 in
  (r1,fppos2)
;;

let mainAnalysis slacDataDir fname sp_tm =
  let noModFlag = ref false in
  let twiceFlag = ref false in
  Ftools.pf_s "FPAnomod" (fun _ -> noModFlag := true) ();
  Ftools.pf_s "FPAtwice" (fun _ -> twiceFlag := true) ();

  Ftools.write_file (slacDataDir ^ "/Fpa/fpretFuncs") [];
  Ftools.write_file (slacDataDir ^ "/Fpa/fpretFuncsR") [];
  
  match !noModFlag,!twiceFlag with
  | true,_ ->
     print_endline "Non-ModularAnalysis mode";
     az.AZ.noMod <- false;
     mainAnalysis_noMod slacDataDir fname sp_tm     
  | false,false ->
     print_endline "ModularAnalysis mode (do Once)";
     let res = mainAnalysis_mod slacDataDir fname sp_tm in
     print_endline "+++ Fnames with fp ret type +++";
     let fpretFuncs: bytes list = Ftools.read_file (slacDataDir ^ "/Fpa/fpretFuncs") in
     let fpretFuncsR: bytes list = Ftools.read_file (slacDataDir ^ "/Fpa/fpretFuncsR") in
     print_list print_string' "," fpretFuncs;
     print_endline "\n+++ Rec Fnames with fp ret type +++";
     print_list print_string' "," fpretFuncsR;
     print_endline "\n++++++++++++++++++++++++++++++++++++";
     res
  | false,true ->
     print_endline "ModularAnalysis mode (do Twice)";
     az.AZ.twice <- true;
     mainAnalysis_mod slacDataDir fname sp_tm     
;;               
  
