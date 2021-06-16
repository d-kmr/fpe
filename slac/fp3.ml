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
            
module FPval = Fpsyntax3.Val
module FPsh = Fpsyntax3.StoreHeap
module FPstate = Fpsyntax3.State
module V = Map.Make(Bytes)
module G = Map.Make(String)
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

let profile_header1 = "";;
let profile_header2 = "| ";;
let profile_header3 = "| | ";;
let profile_header4 = "| | | ";;

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
      mutable globalVars : bytes list;
      mutable deplistFile : bytes;
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
      globalVars = [];
      deplistFile = "";
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

  let println_funtable (funtable: funTable) =
    V.iter (fun fname (modname,mod_id,pos) ->
        print_endline @@ fname ^ " @ {" ^ modname ^ ", modId:" ^ (string_of_int mod_id) ^ ", pos:" ^ (string_of_int pos) ^ "}"
      )
      funtable

  let println_structInfo structInfo =
    V.iter (fun _ structure -> Kstructure.println structure) structInfo
    
  let println_strAliases strAliases =
    V.iter (fun alias strName -> print_endline (alias ^ " => " ^ strName)) strAliases
    
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
       (*
       print_endline @@ "Definition Conflict: " ^ func ^ " :: " ^ cfile1 ^ " " ^ cfile2 ^ " (handled as a missing func)";
        *)
       None
  in
  V.merge f ftbl0 ftbl1
;;


module FpPos = struct

  type t = ((bytes * bytes * int) * FPval.t) list

  let empty = []
         
  let println fppos =
    let print_f_one ((funF,fp,pos),v) =
      print_string' @@ "(" ^ fp ^ "!" ^ (string_of_int pos) ^ "@" ^ funF ^ ")->";
      FPval.println v
    in
    List.iter print_f_one fppos

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
            | SYN (* syntactical analysis *)
            | FPASYN (* syntactical analysis in FPA-mode *)
            
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
      mutable knownList : bytes list;
      mutable currentFunc : bytes;
      mutable mode : mode;
      mutable skipFunclist : bytes list; (* Skip function list for ModRec0-mode *)
      mutable fppos : FpPos.t;
    }

  let println_fppos az = FpPos.println az.fppos
    
  let inclLocalVarCtr az =
    az.localVarCtr <- az.localVarCtr + 1
    
  let add_show_funstack fname az =
    az.funstack <- fname :: az.funstack;
    let fstack = List.rev az.funstack in
    print_string' ">>> ";
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
    }

  let reset mode az =
    az.funstack <- [];
    az.whilestack <- [false];
    az.localVarCtr <- 0;
    az.currentFunc <- "";
    az.mode <- mode;
    az.skipFunclist <- []

  let isKnown az fname = List.mem fname az.knownList
    
    (*
  let isKnown az fname =
    let rec aux knownlist =
      match knownlist with
      | [] -> false
      | (VcpAllC.NONREC f)::_ when f = fname -> true
      | (VcpAllC.REC fnameL)::_ when List.mem fname fnameL -> true
      | _ :: knownlist1 -> aux knownlist1
    in
    aux az.knownList
     *)
    
    (*
  let knownlist_flatten az =
    List.fold_left
      (fun fnameL frec ->
        match frec with
        | VcpAllC.NONREC f -> f :: fnameL
        | VcpAllC.REC fnameL1 -> union fnameL1 fnameL
      )
      []
      az.knownList
     *)
    
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
    match az.AZ.mode with
    | AZ.NOMODE -> ""
    | AZ.GLOBAL -> "GLOBAL"
    | AZ.FPA -> "FPA"
    | AZ.SYN -> "SYN"
    | AZ.FPASYN -> "FPA>SYN"              
  in
  let fname = az.AZ.currentFunc in
  let funLoc =
    match az.AZ.mode,fst loc,fname with
    | AZ.FPA,"","" -> ""
    | AZ.FPA,"",_ -> " " ^ fname
    | AZ.FPA,_,"" -> " " ^ (Klocs.to_string loc)
    | AZ.FPA,_,_ -> " " ^ fname ^ " " ^ (Klocs.to_string loc)
    | _,_,_ -> " " ^ fname
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
          (tp,fld,[FPval.Sname sname])
       | false,true,Kinit.None ->
          (tp,fld,[FPval.Fname []])
       | false,true,Kinit.S exp ->
          let value = FPsh.evalCExpFp loc strV straliases funtable sh exp in          
          (*
          if structName = "special" then print_endline (fld ^ " aaaaaaaaaaaaaaaaaaaa");
          FPval.println value;
           *)
          (tp,fld,value)
       | false,true,_ -> failwith "allocTypeFP: unexpected Init-3"
       | false,false,_ ->
          (*
          if structName = "special" then print_endline (fld ^ " bbbbbbbbbbbbbbbbbbbbb");
           *)
          (tp,fld,FPval.none)
     in
     let preheap0: FPsh.preheap =
       let cell0 = List.map mkPreHeapBody fldTpInitL in
       let cell1 = List.filter (fun (tp,_,_) -> Kexp.isFpType tp) cell0 in
       let cell2 = List.map (fun (_,fld,value) -> (fld,value)) cell1 in
       [ (realStrName, cell2) ]
     in
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
  type retVal_t = FPval.t             
  type fnames_t = bytes list              
  type argRecord_t = fnames_t list (* argument record: F(t1,t2) -> [sh(t1),sh(t2)] *)
  type fpRefRecord_t = (Kexp.t * fnames_t) list (* fp-ref.rec.: t->fp with its value fnameL is saved as (t->fp,fnameL) *)
  type history_t = (argRecord_t * fpRefRecord_t) list
  type t = fpr_t * fpm_t * fn_t * retVal_t * history_t

  let empty = ([],[],[],FPval.none,[])
         
  let init () : t = empty
  let print_fpr (fpr: fpr_t) = List.iter (fun fpr -> print_string' profile_header3; Kexp.println fpr) fpr

  let print_fpm (fpm: fpm_t) = List.iter (fun fpm -> print_string' profile_header3; Kexp.println_lval fpm) fpm
                    
  let print_fn (fn: fn_t) =
    if fn = [] then ()
    else
      begin
        print_string' profile_header3;
        print_list print_string' " " fn;
        print_endline ""
      end
    
  let println_history (history : history_t) =
    List.iter
      (fun (argRec,fpRefRec) ->
        print_endline @@ profile_header3 ^ "Args:";
        println_list'
          (fun fnameL -> print_string' (profile_header3 ^ "{"); (print_list print_string' "," fnameL); print_string' "}") "," argRec;
        print_endline @@ profile_header3 ^ "RefRecords:";
        List.iter
          (fun (e,fnameL) ->
            print_string' profile_header4;
            print_string' "(";
            Kexp.print e;
            print_string' ", {";
            print_list print_string' "," fnameL;
            print_endline "})";
          )
          fpRefRec;
      )
      history

  let println prof =
    let (fpr,fpm,fn,retVal,history) = prof in
    print_endline @@ profile_header2 ^ "[FPR]";
    print_fpr fpr;
    print_endline @@ profile_header2 ^ "[FPM]";
    print_fpm fpm;
    print_string' @@ profile_header2 ^ "[FN] ";
    print_endline @@ (string_of_int (List.length fn)) ^ "-functions";
    (*
    print_fn fn;
     *)
    print_endline @@ profile_header2 ^ "[retVal]";
    print_string' profile_header3;
    FPval.println retVal;
    print_endline @@ profile_header2 ^ "[history]";
    println_history history
    
  let println_opt prof_opt =
    match prof_opt with
    | None -> ()
    | Some prof -> println prof
    
  let rec isFpHolder exp = (* exp's type must be a function-pointer type *)
    match exp with
    | Kexp.Lval lval -> isFpHolder_lval lval
    | _ -> false
  and isFpHolder_lval lval = (* lval's type must be a function-pointer type *)
    match lval with
    | Kexp.Var(_,tp) when Kexp.isFpType tp && Kexp.isGlobal tp -> true 
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
        print_warn ("",0) @@ "Profile of "^fname^" is not found --> empty profile";
        Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) empty;
        empty
      end

  let checkExist fname =
    let file = gi.GI.fpaFunProfileDir ^ "/" ^ fname in 
    match Sys.file_exists file with
    | true -> true
    | false -> print_endline @@ "Checking " ^ file ^ " ---> NO"; false
      
  let getFprFpmFn fname : fpr_t * fpm_t * fn_t =
    let (fpr,fpm,fn,_,_) = get fname in
    (fpr,fpm,fn)

  let getFpr fname : fpr_t =
    let (fpr,_,_,_,_) = get fname in
    fpr

  let getFprL fnameL =
    List.fold_left
      (fun fpr f -> Tools.union fpr (getFpr f))
      []
      fnameL
    
  let getFpm fname : fpm_t =
    let (_,fpm,_,_,_) = get fname in
    fpm

  let getRetVal fname : retVal_t =
    let (_,_,_,retVal,_) = get fname in
    retVal
    
  let getHistory fname : history_t =
    let (_,_,_,_,history) = get fname in
    history

  (* size of a profile *)
  let getSize (prof : t) =
    let (fpr,fpm,fn,retVal,history) = prof in
    let fprSize = List.length fpr in
    let fpmSize = List.length fpm in
    let fnSize = List.length fn in
    let historySize = List.length history in
    fprSize + fpmSize + fnSize + historySize

  let getSizeL profL = List.fold_left (fun n prof -> n+(getSize prof)) 0 profL
                     
  let load_show fnameL =
    match fnameL with
    | [fname] ->
        print_endline (profile_header1 ^ "PROFILE of " ^ fname);
        println (get fname)
    | fname :: _ ->
        print_endline (profile_header1 ^ "PROFILE of {" ^ (string_of_list (fun x->x) "," fnameL) ^ "}");
        println (get fname)
    | _ -> ()

  let updateHistory_save loc fname sh eeArgs fprUX (prof : t) : t =
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
    let (fpr,fpm,fn,retVal,history) = prof in
    let eeArgs' = List.filter Kexp.isFpFun eeArgs in
    let argFnameL =
      List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) eeArgs' in
    let fpRefFnameL =
      List.map
        (fun e ->
          let fnameL = FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh e in
          (e,fnameL))
        fprUX
    in
    let history' =
      if isNew (argFnameL,fpRefFnameL) history
      then (argFnameL,fpRefFnameL)::history
      else history
    in
    let prof1 = (fpr,fpm,fn,retVal,history') in
    Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) prof1;
    prof1

  let updateFn loc fnameFnL (prof: t) : t =
    let (fpr,fpm,fn,retVal,history) = prof in
    let fn' = Tools.union fnameFnL fn in
    (fpr,fpm,fn',retVal,history)

  let updateFpr loc gi ee (prof: t) : t =
    let (fpr,fpm,fn,retVal,history) = prof in
    let strV = gi.GI.structs in
    let aliases = gi.GI.straliases in
    let eeFpHolder = Kexp.getFpHolderL strV aliases ee in
    let fpr' = Tools.union eeFpHolder fpr in
    (fpr',fpm,fn,retVal,history)

  let updateFpm loc gi lvalL (prof: t) : t =
    let updateOne lval prof =
      let (fpr,fpm,fn,retVal,history) = prof in
      let strV = gi.GI.structs in
      let aliases = gi.GI.straliases in
      let eeFpHolder_lval = Kexp.getFpHolder_lval strV aliases lval in
      let fpm' = Tools.union eeFpHolder_lval fpm in
      (fpr,fpm',fn,retVal,history)
    in
    let prof' = List.fold_left (fun prof1 lval1 -> updateOne lval1 prof1) prof lvalL in
    prof'
       
  (* mkFpc sh fname = Union{ sh(e) | e in FPR(fname)} union FN(fname) *)
  (* FPC(sh,F) *)
  let mkFpc sh fname : fpc_t =
    let loc = ("",0) in
    let (eeFpr,_,fn) = getFprFpmFn fname in
    let fnameLL = List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) eeFpr in
    unionL (fn :: fnameLL)

  let mkFpcL sh fnameL = unionL (List.map (mkFpc sh) fnameL)
        
  let read_many fnameL : t list =
    let profL = 
      List.fold_left
        (fun profL fname ->
          let prof : t = Ftools.read_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) in
          profL @ [prof]
        )
        []
        fnameL
    in
    profL
    
end
;;

let print_sub sub =
  List.iter
    (fun (x,v) -> print_string' (x ^ ":="); FPval.println v)
    sub
;;  


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
(* This is used for MemFuncp mode: INPUT=(sh,None,decl,loc), OUTPUT=(sh,None)  *)         
let funcp_decl loc decl sh: FPsh.t = 
  let Kdecl.Decl (tpOut,lval,init) = Kdecl.shift_ptr_left decl in 
  
  match lval,init with
  (* global function pointer without init --> make an entry *)    
  | Kexp.Var (fp,tp),Kinit.None when Kexp.isFpType tp && az.AZ.mode = AZ.GLOBAL ->
     print_mes loc @@ "DECL" ^ (Kdecl.to_string 0 decl);
     let (s,h) = sh in
     let s1: FPsh.store = FPsh.updateFP_s loc s fp [FPval.Fname []] in
     let sh1 = (s1,h) in
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     sh1
  (* Declarations without init --> do nothing *)
  | _,Kinit.None ->
     sh
    
  (* struct type variable with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructType tp) ->   
     let preheap = allocTypeFP loc sh (tp,[-1]) init in
     let sh' = FPsh.update_by_preheap_sh sh preheap in
     sh'
     
  (* struct type array with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructArrayType tp) ->
     let dim = Kexp.extract_dim' tp in
     let tp_iDim =
       try
         (fun (tp,ee) -> (tp,List.map (FPsh.evalCExpInt loc sh) ee)) dim
       with
         UNKNOWN -> (tp,[1]) (* dummy *)
     in
     let preheap = allocTypeFP loc sh tp_iDim init in
     let sh' = FPsh.update_by_preheap_sh sh preheap in     
     sh'
     
  (* simple type array with init --> do nothing *)
  | Kexp.Var (v,tp),_ when (Kexp.isSimpleArrayType tp) ->
     sh

  (* function pointer with init *)
  | Kexp.Var (arr,tp),_ when Kexp.isFpType tp && Kexp.hasArray tp ->
     (* print_mes loc "-- fp-decl case-4.1a: function-pointer array case"; *)
     let (s,h) = sh in
     let rec getExpL init =
       match init with
       | Kinit.S e -> [e]
       | Kinit.M initL -> unionL (List.map getExpL initL)
       | Kinit.None -> []
     in
     let ee = getExpL init in
     let fnameL = unionL (List.map (FPsh.evalCExpFp_fnameL loc gi.GI.structs gi.GI.straliases gi.GI.funtable sh) ee) in
     let (h1,_) = FPsh.updateUnionFpFlag_h loc h "*" "*" [FPval.Fname fnameL] in
     let sh1 = (s,h1) in     
     sh1
     
  (* function pointer with init *)
  | Kexp.Var (fp,tp),_ when Kexp.isFpType tp ->
     (* print_mes loc "-- fp-decl case-4.1b: function-pointer case"; *)
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
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     sh1

  (* Function prototype case --> do nothing (This case does not happen) *)
  | Kexp.Var (fname,tp),_ when Kexp.hasFunc tp ->
     (* print_mes loc "-- fp-decl case-4.2: function-prototype case (do nothing)"; *)
     sh
     
  (* other cases --> do nothing *)
  | _,_ ->
     sh
;;               

(* Syntactic Analysis for declarations *)
(* Used for Syntactical-Analysis mode: INPUT=(az,sh,Some fundata,decl,loc), OUTPUT=(sh,Some fundata)  *)
let synAnalysis_decl loc decl (prof : FunProfile.t) : FunProfile.t =
  let Kdecl.Decl (tpOut,lval,init) = Kdecl.shift_ptr_left decl in
  (* print_mes loc (Kdecl.to_string 0 decl); *)
  match lval,init with
  (* Declarations without init --> do nothing *)
  | _,Kinit.None ->
     prof
  (* struct type variable with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructType tp) ->
     (* CHECK THIS 2021.01.20 *)
     prof
  (* struct type array with init *)
  | Kexp.Var (v,tp),_ when (Kexp.isStructArrayType tp) ->
     prof
  (* simple type array with init --> do nothing *)
  | Kexp.Var (v,tp),_ when (Kexp.isSimpleArrayType tp) ->
     prof
  (* function pointer with init *)
  | Kexp.Var (arr,tp),_ when Kexp.isFpType tp && Kexp.hasArray tp ->
     let rec getExpL init =
       match init with
       | Kinit.S e -> [e]
       | Kinit.M initL -> unionL (List.map getExpL initL)
       | Kinit.None -> []
     in
     let ee = getExpL init in
     let prof1 = FunProfile.updateFn loc (unionL (List.map Kexp.getFunName ee)) prof in
     let prof2 = FunProfile.updateFpr loc gi ee prof1 in
     let prof3 = FunProfile.updateFpm loc gi [Kexp.Ptr Kexp.Unknown] prof2 in (* "*" is added to FPM *)
     print_mes loc @@ "FPM: " ^ "*";
     print_mes loc @@ "FPR: " ^ (string_of_list Kexp.to_string "," ee);
     prof3
  (* function pointer with init *)
  | Kexp.Var (fp,tp),_ when Kexp.isFpType tp ->
     let (fpr0,fpm0,fn0,retVal,history) = prof in
     let prof1 =
       match init with
       | Kinit.S exp when FunProfile.isFpHolder exp ->
          let fpr1 = exp :: fpr0 in
          let fpm1 = lval :: fpm0 in
          print_mes loc @@ "FPM: " ^ fp;
          print_mes loc @@ "FPR: " ^ (Kexp.to_string exp);
          (fpr1,fpm1,fn0,retVal,history)
       | Kinit.M [Kinit.S exp] when FunProfile.isFpHolder exp ->
          let fpr1 = exp :: fpr0 in
          let fpm1 = lval :: fpm0 in
          print_mes loc @@ "FPM: " ^ fp;
          print_mes loc @@ "FPR: " ^ (Kexp.to_string exp);
          (fpr1,fpm1,fn0,retVal,history)
       | Kinit.S exp ->
          let profA = FunProfile.updateFn loc (Kexp.getFunName exp) prof in
          let profB = FunProfile.updateFpr loc gi [exp] profA in
          print_mes loc @@ "FPM: " ^ fp;
          print_mes loc @@ "FPR: " ^ (Kexp.to_string exp);
          profB
       | _ -> prof
     in
     prof1
  (* Function prototype case --> do nothing (This case does not happen) *)
  | Kexp.Var (fname,tp),_ when Kexp.hasFunc tp ->
     prof
  (* other cases --> do nothing *)
  | _,_ ->
     prof
;;               

(*
let minor = ref 0.0;;
 *)
let makeDependencyList_fork fname =
  let loc = ("",0) in
  let knownlistSize = string_of_int (List.length az.AZ.knownList) in
  print_mes ~opt:"ALWAYS" loc @@ "Start generating DepList for " ^fname^ " (knownlist size: " ^knownlistSize^ ")";
  let aux () = 
    let pid = Unix.fork () in
    match pid with
    | 0 -> (* child process *)
       begin
         try
           let mods = gi.GI.fmodules in
           let (_,saved_calls) : VcpDep.rec_t list * bytes list G.t = Ftools.read_file gi.GI.deplistFile in
           let (deplist,newcalls) = VcpDep.get_dependency_set_of_list ~mods:mods saved_calls fname az.AZ.knownList in
           Ftools.write_file gi.GI.deplistFile (deplist,newcalls);
           exit 0
         with
         | Sys_error mes -> failwith ("exception from child Sys_err " ^ mes)
         | _ -> failwith "exception from child"
       end;
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
  let (deplist,calls) : VcpDep.rec_t list * bytes list G.t = Ftools.read_file gi.GI.deplistFile in
  (* let callsSize = G.fold (fun _ fnameL n -> n+(List.length fnameL)) calls 0 in *)
  (* print_mes ~opt:"ALWAYS" loc @@ "End generating DepList for " ^ fname ^ " (finished call size: " ^ (string_of_int callsSize) ^ ")";  *)
  print_mes ~opt:"ALWAYS" loc @@ "End generating DepList for " ^ fname;
  deplist
;;

(*========================================*)
(* funcp for statement *)
(*========================================*)
(* Syntactical Analysis *)
(* (prof_opt,fnameL) : fnameL is the list of function names that are called as function calls *)
let rec synAnalysisShallow fname stmt prof_fnameL =
  az.AZ.currentFunc <- fname;
  let strV = gi.GI.structs in
  let aliases = gi.GI.straliases in
  let (prof,fnameL) = prof_fnameL in
  match stmt with
  | Kstmt.Decl (decl,loc) ->     
     Ftools.pf_s "FPAfindbranch" print_endline "br-Decl";
     let prof' = synAnalysis_decl ("",0) decl prof in
     (prof',fnameL)
  (* { P1;P2;P3 } *)
  | Kstmt.Block (stmtL,loc) ->
     let prof_fnameL1 = 
       List.fold_left
         (fun prof_fnameL stmt ->
           synAnalysisShallow fname stmt prof_fnameL
         )
         prof_fnameL
         stmtL
     in
     prof_fnameL1
  (* IF-THEN-statement *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) when Kstmt.isSkip stmtElse ->
     (* print_mes loc @@ "IF-THEN"; *)
     let prof_fnameL1 = synAnalysisShallow fname stmtThen prof_fnameL in
     prof_fnameL1
  (* IF-THEN-ELSE statement *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) ->
     (* print_mes loc @@ "IF-THEN-ELSE"; *)
     let prof_fnameL1 = synAnalysisShallow fname stmtThen prof_fnameL in
     let prof_fnameL2 = synAnalysisShallow fname stmtElse prof_fnameL1 in
     prof_fnameL2
  (* Others *)
  | Kstmt.Lbl (_,_,loc)     -> prof_fnameL
  | Kstmt.Fail loc          -> prof_fnameL
  | Kstmt.Break loc         -> prof_fnameL
  | Kstmt.Continue loc      -> prof_fnameL
  | Kstmt.Unknown loc       -> prof_fnameL
  | Kstmt.Return (e,loc)    -> prof_fnameL
  | Kstmt.Skip              -> prof_fnameL
  | Kstmt.Malloc (_,_,_,_)  -> prof_fnameL
  | Kstmt.Free (t,loc)      -> prof_fnameL
  (* fp = t->fld *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),Kexp.Lval (Kexp.Arrow (u,tpStruct,fld)),loc) when Kexp.isFpType tp  ->
     let lval = Kexp.Var (fp,tp) in
     let eFld = Kexp.Lval (Kexp.Arrow (u,tpStruct,fld)) in
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName eFld) prof in
     let prof2 = FunProfile.updateFpr loc gi [eFld] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     print_mes loc @@ "FPM: " ^ fp;
     print_mes loc @@ "FPR: " ^ (Kexp.to_string eFld);
     (prof3,fnameL)
  (* fp = t *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),t,loc) when Kexp.isFpType tp  || Kexp.isFun t ->
     let lval = Kexp.Var (fp,tp) in
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName t) prof in
     let prof2 = FunProfile.updateFpr loc gi [t] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval]  prof2 in
     print_mes loc @@ "FPM: " ^ fp;
     print_mes loc @@ "FPR: " ^ (Kexp.to_string t);
     (prof3,fnameL)
  (* x = t *)
  | Kstmt.Asgn (Kexp.Var (x,tp),t,loc) ->
     let lval = Kexp.Var (x,tp) in     
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName t) prof in
     let prof2 = FunProfile.updateFpr loc gi [t] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     (prof3,fnameL)
  (* t<tp>->f = u; *)
  | Kstmt.Asgn (Kexp.Arrow (t,tp,fld),u,loc) ->
     print_mes loc @@ "FPM: " ^ (Kexp.to_string_lval (Kexp.Arrow (t,tp,fld)));
     if FunProfile.isFpHolder u then print_mes loc @@ "FPR: " ^ (Kexp.to_string u);
     let lval = Kexp.Arrow (t,tp,fld) in
     begin       
       match Kexp.getTrueType_lval_opt gi.GI.structs aliases lval with
       | Some tp1 when Kexp.isFpType tp1 ->
          (* updating profile *)
          let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in
          let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
          let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
          (prof3,fnameL)
       | _ ->
          (* updating profile *)
          let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in
          let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
          let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
          (prof3,fnameL)
     end
  (* *fp = u; *)
  | Kstmt.Asgn (Kexp.Ptr (Kexp.Lval (Kexp.Var(fp,tp))),u,loc) when Kexp.isFpType tp ->
     (* updating profile *)
     let lval = Kexp.Ptr (Kexp.Lval (Kexp.Var(fp,tp))) in
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in
     let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     print_mes loc @@ "FPM: " ^ fp;
     if FunProfile.isFpHolder u then print_mes loc @@ "FPR: " ^ (Kexp.to_string u);     
     (prof3,fnameL)
  (* *e = u; where e has a function pointer *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) when Kexp.hasFunPtrTp strV aliases t ->
     let lval = Kexp.Ptr t in     
     (* updating profile *)
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in
     let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     (prof3,fnameL)
  (* *t = u; --> do nothing *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) ->
     let lval = Kexp.Ptr t in     
     (* updating profile *)
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in
     let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     (prof3,fnameL)
  (* arr[t1][t2] = u; --> do nothing since this form would not come *)
  | Kstmt.Asgn (Kexp.Array (aLval,tt),u,loc) ->
     let lval = Kexp.Array (aLval,tt) in     
     (* updating profile *)
     let prof1 = FunProfile.updateFn loc (Kexp.getFunName u) prof in     
     let prof2 = FunProfile.updateFpr loc gi [u] prof1 in
     let prof3 = FunProfile.updateFpm loc gi [lval] prof2 in
     (prof3,fnameL)
  (* while(b) P; *)
  | Kstmt.While (_,_,stmtBody,loc) ->
     (* print_mes loc @@ "WHILE"; *)
     let prof_fnameL1 = synAnalysisShallow fname stmtBody prof_fnameL in
     prof_fnameL1
  (* Missing functions *)
  | Kstmt.Fcall (fname,_,_,_,loc) when List.mem fname az.AZ.missingFunlist ->
     print_mes loc "FCALL (missing)";
     prof_fnameL
  (* Special handling functions *)
  | Kstmt.Fcall (fname,tt,_,_,loc) when isDebugFun(fname) ->
     prof_fnameL
  (* Function Pointer Call --> create an entry of fppos and skip *)
  | Kstmt.FPcall (fp,pos,tt,tpRet,tpPrm,loc) ->
     print_mes loc @@ ("FpCALL: " ^ fp ^ "!" ^ (string_of_int pos)); 
     let prof_fnameL1 = 
       if List.mem fp gi.GI.globalVars
       then
         let eFp = Kexp.Lval (Kexp.Var (fp,[Kexp.OTHER "GLOBAL";Kexp.FUNCPTR ([],[])])) in
         let prof1 = FunProfile.updateFpr loc gi [eFp] prof in
         (prof1,fnameL)
       else
         prof_fnameL
     in
     (* create a fppos entry *)
     azUpdateFppos loc fname fp pos FPval.none;
     prof_fnameL1
  (* Function Call *)
  | Kstmt.Fcall (fname,eeArg,tpRet,_,loc) ->
     print_mes loc @@ ("FCALL: " ^ fname);
     let fnameL_arg = Kexp.getFunNameL eeArg in     
     let prof1 = FunProfile.updateFpr loc gi eeArg prof in
     let prof2 = FunProfile.updateFn loc (fname::fnameL_arg) prof1 in
     (prof2,(fname::fnameL))
;;         

(* Syntactical Analysis main part : this may raise exceptions (Skip) *)
let syntacticalAnalysis fname = 
  let loc = ("",0) in
  az.AZ.currentFunc <- fname;
  let getFunBody fname =
    match GI.getFundefBody gi fname with
    | None -> None
    | Some (tpRet,declPrms,stmtBody) -> Some stmtBody
  in
  let analyzerFile = gi.GI.slacDataDir ^ "/Fpa/analyzer" in
  
  let aux dep =
    let pid = Unix.fork () in
    match pid with
    | 0 -> (* child process *)
       begin
         try
           match dep with
           | VcpDep.NONREC fnameG ->
              (* Non-Recursive function case*)
              print_mes ~opt:"ALWAYS" ("",0) ("START Syntactical Analysis of " ^ fnameG);
              begin
                match getFunBody fnameG with
                | None ->
                   print_mes ~opt:"ALWAYS" ("",0) (fname ^ " is a missing function --> added to MissingList and create an EmptyProfile\n");
                   az.AZ.missingFunlist <- Tools.union az.AZ.missingFunlist [fnameG];
                   az.AZ.knownList <- fnameG :: az.AZ.knownList;
                   Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fnameG) FunProfile.empty;
                   Ftools.write_file analyzerFile az;
                   exit 0
                | Some stmtBody ->
                   let prof0 = FunProfile.empty in
                   let (prof1,fnameL1) = synAnalysisShallow fnameG stmtBody (prof0,[]) in
                   let prof2 =
                     List.fold_left
                       (fun profA fname ->
                         let (fpr,fpm,fn,retVal,_) = FunProfile.get fname in
                         let profA1 = FunProfile.updateFn loc fn profA in
                         let profA2 = FunProfile.updateFpr loc gi fpr profA1 in
                         let profA3 = FunProfile.updateFpm loc gi fpm profA2 in
                         profA3
                       )
                       prof1
                       fnameL1
                   in
                   Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fnameG) prof2;
                   Ftools.pf_s "FPAdebug" FunProfile.load_show [fnameG];
                   print_mes ~opt:"ALWAYS" loc ("Profile of " ^ fnameG ^ " is saved");
                   az.AZ.knownList <- fnameG :: az.AZ.knownList;
                   let knownlistSize = string_of_int (List.length az.AZ.knownList) in
                   print_mes ~opt:"ALWAYS" ("",0)
                     ("FINISH Syntactical Analysis of " ^ fnameG ^ " (added to knownlist (size: " ^ knownlistSize ^ "))\n");
                   Ftools.write_file analyzerFile az;
                   exit 0
              end
           | VcpDep.REC fnameL ->
              (* Recursive-function case: {F1,F2,F3} *)
              let fnameSet = "{" ^ (string_of_list (fun x->x) "," fnameL) ^ "}" in
              print_mes ~opt:"ALWAYS" ("",0) ("Syntactical Analysis of " ^ fnameSet);
              Ftools.pf_s "FPAdebug" print_endline "Recursive function case";
              (* Shallow Syntactical Analysis of fnameL *)
              let stmtBodyL =
                List.fold_left
                  (fun stmtL f -> match getFunBody f with Some stmt -> stmt :: stmtL | None -> failwith "no-such-case")
                  []
                  fnameL
              in
              let (prof1,calledFnameL) =
                List.fold_left
                  (fun prof_fnameL (fname,stmt) ->
                    synAnalysisShallow fname stmt prof_fnameL
                  )
                  (FunProfile.empty,[])
                  (zipLst fnameL stmtBodyL)
              in
              let calledFnameL1 = setminus calledFnameL fnameL in
              (* Adding profiles of the referred functions *)
              let prof2 =
                List.fold_left
                  (fun profA fname ->
                    let (fpr,fpm,fn,_,_) = FunProfile.get fname in
                    let profA1 = FunProfile.updateFn loc fn profA in
                    let profA2 = FunProfile.updateFpr loc gi fpr profA1 in
                    let profA3 = FunProfile.updateFpm loc gi fpm profA2 in
                    profA3
                  )
                  prof1
                  calledFnameL1
              in
              List.iter
                (fun fname -> Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) prof2)
                fnameL;
              Ftools.pf_s "FPAdebug" FunProfile.load_show fnameL;
              az.AZ.knownList <- Tools.union az.AZ.knownList fnameL;              
              let knownlistSize = string_of_int (List.length az.AZ.knownList) in
              print_mes ~opt:"ALWAYS" ("",0)
                ("FINISH Syntactical Analysis of " ^ fnameSet ^ " (added to knownlist (size: " ^ knownlistSize ^ "))\n");
              Ftools.write_file analyzerFile az;              
              exit 0
         with
           _ ->
           let fnameL = match dep with VcpDep.NONREC fnameG -> [fnameG] | VcpDep.REC fnameL -> fnameL in
           az.AZ.knownList <- Tools.union fnameL az.AZ.knownList;
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
  let deplist = makeDependencyList_fork fname in  
  let stack = ref (List.rev deplist) in
  while !stack <> [] do
    let dep = List.hd !stack in
    stack := List.tl !stack;
    aux dep;
  done;
  ()
;;

let skipCheck loc curUX fprUX sh eeArg fname =
  Ftools.pf_s "FPAdebug" print_endline "Skip check starts";
  let aliases = gi.GI.straliases in
  let funtable = gi.GI.funtable in
  let strV = gi.GI.structs in
  (* History Check *)
  let history = FunProfile.getHistory fname in
  let checkHistory () =
    let checkArg argRec =
      let eeArg' = List.filter Kexp.isFpFun eeArg in
      let fnamesArg = List.map (FPsh.evalCExpFp_fnameL loc strV aliases funtable sh) eeArg' in
      List.for_all
        (fun (fnames_now,fnames_prev) ->
          match subset fnames_now fnames_prev with
          | true -> true
          | false ->
             print_endline "checkHistory (argument check): not (Now < Old)";
             print_string' "Now: "; println_list print_string' " " fnames_now;
             print_string' "Old: "; println_list print_string' " " fnames_prev;
             false
        )
        (zipLst fnamesArg argRec)
    in
    let checkFpRef fpRefRec =
      let eeFprOld = List.map fst fpRefRec in
      let rec aux fprUX1 =
        match fprUX1 with
        | [] -> true
        | eFpr :: fprUX2 when List.mem eFpr eeFprOld ->
           let fnames_now = FPsh.evalCExpFp_fnameL loc strV aliases funtable sh eFpr in
           let fnames_old = List.assoc eFpr fpRefRec in
           begin
             match subset fnames_now fnames_old with
             | true -> aux fprUX2
             | false -> false
           end
        | eFpr :: fprUX2 ->
           print_endline "******************";           
           print_endline "checkHistory (Fpr check): not (Now < Old)";
           Kexp.print eFpr;
           print_endline " is a new one";
           List.iter (fun (w,fnameL) -> Kexp.println w) fpRefRec;
           (*
           print_endline "***";
           List.iter Kexp.println fprUX;
           print_list print_string' " " curUX;
            *)
           print_endline "******************";
           false
      in
      aux fprUX
    in
    let checkHistoryOne (argRec,fpRefRec) =
      (checkArg argRec) && (checkFpRef fpRefRec)
    in
    List.exists checkHistoryOne history
  in
  let res =
    match checkHistory () with
    | true -> 
       Ftools.pf_s "FPAdebug" print_endline "CheckSkip: History check ... OK";
       true
    | false ->
       let mes = if history = [] then " (history of " ^ fname ^ " is empty)" else "" in
       Ftools.pf_s "FPAdebug" print_endline ("CheckSkip: History check ... NO" ^ mes);
       false
  in
  Ftools.pf_s "FPAdebug" print_endline "Skip check ends";
  res
;;

let fork_ctr = ref 0
;;
let rec funcp_stmt sp_tm stmt r: FPstate.t =
  match r with
  | FPstate.None -> FPstate.None
  | FPstate.SH sh -> funcp_stmt_sh sp_tm stmt sh
                   
and funcp_stmt_sh sp_tm stmt sh =
  (* let minor' = !minor in *)
  let (s,h) = sh in
  let r = FPstate.SH sh in
  let strV = gi.GI.structs in
  let aliases = gi.GI.straliases in
  let funtable = gi.GI.funtable in
  let res =
  match stmt with
  | Kstmt.Decl (decl,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Decl";
     let sh' = funcp_decl loc decl sh in
     let r1 = FPstate.SH sh' in
     r1
  (* Skip --> do nothing *)
  | Kstmt.Skip -> r
  (* v = malloc(sizeof(tp)*t); --> do nothing *)
  | Kstmt.Malloc (v,tp,t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Malloc";
     r
  (* free(t); --> do nothing *)
  | Kstmt.Free (t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Free";
     r
  (* { P1;P2;P3 } *)
  | Kstmt.Block (stmtL,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Block";
     let r1 =
       List.fold_left
         (fun r0 stmt0 -> funcp_stmt sp_tm stmt0 r0)
         r
         stmtL
     in
     r1
  (* IF-THEN-statement *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) when Kstmt.isSkip stmtElse ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-If-Then";
     (* print_mes loc "IF-Then-statement"; *)
     (* print_mes loc "Begin THEN"; *)
     let r1 = funcp_stmt_sh sp_tm stmtThen sh in
     (* print_mes loc "End THEN"; *)
     r1
  (* IF-THEN-ELSE statement *)
  | Kstmt.If (_,stmtThen,stmtElse,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-If-seq";
     (* print_mes loc "IF-statement"; *)
     let r1 = 
       (* print_mes loc "Begin THEN"; *)
       match funcp_stmt_sh sp_tm stmtThen sh with
       | FPstate.None ->
          (* print_mes loc "End THEN"; *)
          r
       | FPstate.SH sh1 ->
          (* print_mes loc "End THEN + Start ELSE"; *)
          let r1 = funcp_stmt_sh sp_tm stmtElse sh1 in
          (* print_mes loc "End ELSE"; *)
          r1
     in
     r1
  (* L:: --> do nothing *)
  | Kstmt.Lbl (_,_,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Label";
     r
  (* Fail --> do nothing *)     
  | Kstmt.Fail loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Fail";
     print_warn loc "fp encounters Fail";
     r
  (* Break --> do nothing *)
  | Kstmt.Break loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Break";
     print_warn loc "fp encounters Break (this should be eliminated by the prog.trans.)";
     r
  (* Condinue --> do nothing *)
  | Kstmt.Continue loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Continue";
     print_warn loc "fp encounters Continue (this should be eliminated by the prog.trans.)";
     r
  (* Unknown --> do nothing *)
  | Kstmt.Unknown loc ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Unknown";
     print_warn loc "fp: encounters Unknown";
     r
  (* return(t); *)
  | Kstmt.Return (e,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Return";
     (*
     print_mes loc (Kstmt.to_string "" 0 stmt);
     print_mes loc "-- funcp_stmt: Return-case";     
      *)
     let r1 = 
       match Kexp.getTrueType_opt strV aliases e with
       | Some tp when Kexp.isFpType tp ->
          let fnameL = FPsh.evalCExpFp_fnameL loc strV aliases funtable sh e in
          let s' = FPsh.updateRetUnionFP_s loc s fnameL in
          FPstate.SH (s',h)
       | _ ->
          FPstate.SH sh
     in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     r1
  (* fp = t->fld *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),Kexp.Lval (Kexp.Arrow (u,tpStruct,fld)),loc) when Kexp.isFpType tp  ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(fp=t->fld)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
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
          print_endline @@ strName ^ "->" ^ fld ^ ": No entry in the heap";
          FPsh.println1_h h strName;
          failwith ""
       | Some value -> value
     in
     let updateFpFlagFun = FPsh.updateUnionFpFlag_s in
     let (s1,updateFlag) = updateFpFlagFun loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     AZ.update_whilestack az updateFlag;
     let r1 = FPstate.SH (s1,h) in
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" (fun _ -> FPsh.println_h_one strName (FPsh.lookup_h aliases sh strName)) ();
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     r1
  (* fp = t *)
  | Kstmt.Asgn (Kexp.Var (fp,tp),t,loc) when Kexp.isFpType tp  || Kexp.isFun t ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(fp=t)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* print_mes loc "-- funcp_stmt: Asgn (function-pointer: fp=t)-case"; *)
     let value = FPsh.evalCExpFp loc strV aliases funtable sh t in
     let updateFpFlagFun = FPsh.updateUnionFpFlag_s in
     let (s1,updateFlag) = updateFpFlagFun loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     let r1 = FPstate.SH (s1,h) in
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- PRE : ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" (fun _ -> print_string' "-- POST: ") ();
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     r1
  (* x = t --> skip *)
  | Kstmt.Asgn (Kexp.Var (x,tp),t,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(x=t)";
     print_mes loc (Kstmt.to_string "" 0 stmt);     
     r
  (* t<tp>->f = u; *)
  | Kstmt.Asgn (Kexp.Arrow (t,tp,fld),u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(t<tp>->f=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     let lval = Kexp.Arrow (t,tp,fld) in
     let r1 = 
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
          let r1 = FPstate.SH sh1 in
          Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
          Ftools.pf_s "FPAdebug" (FPsh.println_h_one strName) (FPsh.lookup_h aliases sh strName);
          Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
          Ftools.pf_s "FPAdebug" (FPsh.println_h_one strName) (FPsh.lookup_h aliases sh1 strName);
          r1
       | _ ->
          Ftools.pf_s "FPAfindbranch" print_endline "br-(t<tp>->f=u)-B";          
          r
     in
   r1
  (* *fp = u; *)
  | Kstmt.Asgn (Kexp.Ptr (Kexp.Lval (Kexp.Var(fp,tp))),u,loc) when Kexp.isFpType tp ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*fp=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     (* print_mes loc "-- funcp_stmt: Asgn (function-pointer2: *fp=u)-case"; *)
     (*     let fp' = tempvar_original_name fp in  *)
     let value = FPsh.evalCExpFp loc strV aliases funtable sh u in
     let (s1,updateFlag) = FPsh.updateUnionFpFlag_s loc s fp value in (* s' = s[fp=s(fp1) cup s(fp)] *)
     let r1 = FPstate.SH (s1,h) in
     (* Ftools.pf_s "FPAdebug" (FPstate.println' "SH > ") r'; *)
     Ftools.pf_s "FPAdebug" print_string' "-- PRE : ";
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s fp);
     Ftools.pf_s "FPAdebug" print_string' "-- POST: ";
     Ftools.pf_s "FPAdebug" FPsh.println_s (FPsh.filter_s s1 fp);
     r1
  (* *e = u; where e has a function pointer *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) when Kexp.hasFunPtrTp strV aliases t ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*fp=u)";
     print_mes loc (Kstmt.to_string "" 0 stmt);
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     print_mes loc "-- funcp_stmt: Asgn (function-pointer2: *e=u with e:FP-type)-case";
     let value = FPsh.evalCExpFp loc strV aliases funtable sh u in
     let (h1,updateFlag) = FPsh.updateUnionFpFlag_h loc h "*" "*" value in (* h1 = h[("*","*"):=h("*","*")+fnameL] *)
     let r1 = FPstate.SH (s,h1) in
     r1
  (* *t = u; --> do nothing *)
  | Kstmt.Asgn (Kexp.Ptr t,u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-(*t=u)";
     (* print_mes loc (Kstmt.to_string "" 0 stmt); *)
     (* print_mes loc "-- funcp_stmt: Asgn [*t=u]-case"; *)
     r
  (* arr[t1][t2] = u; --> do nothing since this form would not come *)
  | Kstmt.Asgn (Kexp.Array (aLval,tt),u,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-Array-assign";
     (* print_mes loc (Kstmt.to_string "" 0 stmt); *)
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     (* print_mes loc "-- funcp_stmt: Asgn (arr[t]=u)-case"; *)
     r
  (* while(b) P; (fixed-point-computation) *)
  | Kstmt.While (_,_,stmtBody,loc) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-19";
     (* print_mes loc "WHILE-statement"; *)
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)     
     let _r = ref r in
     begin
       try
         while true do
           AZ.push_whilestack az;
           _r := funcp_stmt sp_tm stmtBody !_r;
           if not (AZ.pop_whilestack az) then raise Exit else ();
         done;
       with
         _ -> ()
     end;
     !_r
  (* Missing functions *)
  | Kstmt.Fcall (fname,_,_,_,loc) when List.mem fname az.AZ.missingFunlist ->
     print_mes loc ("FCALL: " ^ fname ^ " is a missing function --> SKIP");
     r
  (* Special handling functions *)
  | Kstmt.Fcall (fname,tt,_,_,loc) when isDebugFun(fname) ->
     Ftools.pf_s "FPAfindbranch" print_endline "br-SP-FunCall";
     print_mes loc (Kstmt.to_string "" 0 stmt);
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
     r
     
  (* (fp)(t1,..,tn) / (#f)(t1,..,tn) : execute FPcall (in FPA-mode) *)
  | Kstmt.FPcall (fp,pos,tt,tpRet,tpPrm,loc) ->
     print_mes loc ("FpCALL: " ^ (Kstmt.to_string "" 0 stmt));
     (* Ftools.pf_s "FPAdebug" (Kstmt.println' cheader) stmt; *)
     let curFunc = az.AZ.currentFunc in     
     let fp' = tempvar_original_name fp in
     begin
       match FPsh.evalFP loc sh fp with (* s(fp) *)
       | [] ->
          C.print_warn loc @@ "FpCall: " ^ fp ^ " is empty!! (skip)";
          r
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
          let r1 = 
            List.fold_left
              (fun r' fname ->
                print_mes loc (fp ^ " is replaced by " ^ fname);
                let stmt1 = Kstmt.Fcall (fname,tt,tpRet,tpPrm,loc) in
                funcp_stmt sp_tm stmt1 r'
              )
              r
              fnameL2
          in
          r1
     end

  (* F(t1,..,tn) / F(t1,..,tn) *)
  | Kstmt.Fcall (fname,eeArg,tpRet,_,loc) ->
     (* print_mes loc (Kstmt.to_string "" 0 stmt); *)
     print_mes loc @@ "FCALL: " ^ fname ^ " --> Do SkipCheck";
     (*     let tm1 = Sys.time () in     *)
     Ftools.pf_s "FPAfindbranch" print_endline "br-FCall";
     let curFunc = az.AZ.currentFunc in
     (* Generation of UX *)
     let curUX =
       let rec aux (cX,cUX,cFPC) =
         match cX with
         | [] -> cUX
         | _ ->
            (* Check whether all profiles of the functions in X exist *)
            List.iter
              (fun f ->
                match List.mem f az.AZ.knownList with
                | true -> ()
                | false -> 
                   print_mes loc @@ "SkipCheck: Profile of " ^ f ^ " is missing --> Do Syntactical Analysis\n";
                   az.AZ.mode <- AZ.FPASYN;
                   syntacticalAnalysis f;
                   az.AZ.mode <- AZ.FPA
              )
              cX;
            let nFPC = FunProfile.mkFpcL sh cX in
            let nUX = Tools.union cUX cX in
            let nX = Tools.setminus nFPC nUX in
            aux (nX,nUX,nFPC)
       in
       aux ([fname],[],[])
     in
     az.AZ.currentFunc <- curFunc;
     let fprUX = FunProfile.getFprL curUX in
     match List.mem fname az.AZ.funstack, skipCheck loc curUX fprUX sh eeArg fname with
     | true,_ ->
        print_mes loc @@ "RECURSIVE CALL!! --> SKIP";
        let (_,_,_,retVal,_) = FunProfile.get fname in     
        let sh1 = FPsh.updateRetVal loc sh retVal in
        let r1 = FPstate.SH sh1 in
        r1
     | _,true -> (* SKIP case *)
        print_mes loc @@ "SkipCheck result: True --> SKIP";
        let (_,_,_,retVal,_) = FunProfile.get fname in     
        let sh1 = FPsh.updateRetVal loc sh retVal in
        let r1 = FPstate.SH sh1 in
        r1
     | _,false -> (* NORMAL case *)
        fork_ctr := !fork_ctr + 1;
        let r' = 
          if false (* !fork_ctr mod 10 = 0 *)
          then
            begin
              print_endline "Fcall: fork is used";
              fcall_body_fork sp_tm loc !fork_ctr fname sh eeArg fprUX r
            end
          else
            fcall_body sp_tm loc fname sh eeArg fprUX r
        in
        r'
        (*
        print_mes loc @@ "SkipCheck result: False";        
        (* Update history *)
        let prof_old = FunProfile.get fname in
        let prof_new = FunProfile.updateHistory_save loc fname sh eeArg fprUX prof_old in
        print_mes loc ("Updating history for " ^ fname);
        Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        Ftools.pf_s "FPAdebug" print_endline (profile_header1 ^ "Previous Profile of " ^ fname);
        Ftools.pf_s "FPAdebug" FunProfile.println prof_old;
        Ftools.pf_s "FPAdebug" print_endline profile_header1;
        Ftools.pf_s "FPAdebug" print_endline (profile_header1 ^ "Updated Profile of " ^ fname);
        Ftools.pf_s "FPAdebug" FunProfile.println prof_new;
        Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
        (**)     
        let tm1 = Sys.time () in
        match GI.getFundefBody gi fname with
        | None ->
           (* No-definition case -> do nothing *)
           print_mes loc @@ fname ^ ": NoDefinition --> Empty profile is created + added to KnownList";
           az.AZ.knownList <- (VcpAllC.NONREC fname) :: az.AZ.knownList;
           az.AZ.missingFunlist <- Tools.union az.AZ.missingFunlist [fname];
           Ftools.write_file (gi.GI.fpaFunProfileDir ^ "/" ^ fname) FunProfile.empty;
           r
        | Some (tpRet,declPrms,stmtBody) ->
           print_mes loc ("Entering " ^ fname);
           (* Pre-processing *)
           print_mes loc (fname ^ " is added to funstack");
           Ftools.pf_s "FPAdebug" (AZ.add_show_funstack fname) az;           
           az.AZ.currentFunc <- fname;
           let sh1 = FPsh.push sh in
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
           let r2 = funcp_stmt_sh sp_tm stmtBody2 sh1 in
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
           let r1 = FPstate.SH sh2a in
           r1
           *)
  in
  res
and fcall_body sp_tm loc fname sh eeArg fprUX r = 
  print_mes loc @@ "SkipCheck result: False";        
  (* Update history *)
  let prof_old = FunProfile.get fname in
  let prof_new = FunProfile.updateHistory_save loc fname sh eeArg fprUX prof_old in
  print_mes loc ("Updating history for " ^ fname);
  Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
  Ftools.pf_s "FPAdebug" print_endline (profile_header1 ^ "Previous Profile of " ^ fname);
  Ftools.pf_s "FPAdebug" FunProfile.println prof_old;
  Ftools.pf_s "FPAdebug" print_endline profile_header1;
  Ftools.pf_s "FPAdebug" print_endline (profile_header1 ^ "Updated Profile of " ^ fname);
  Ftools.pf_s "FPAdebug" FunProfile.println prof_new;
  Ftools.pf_s "FPAdebug" print_endline "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@";
  (**)     
  let tm1 = Sys.time () in
  match GI.getFundefBody gi fname with
  | None ->
     (* No-definition case -> do nothing *)
     print_mes loc @@ fname ^ ": NoDefinition --> Skip";
     r
  | Some (tpRet,declPrms,stmtBody) ->
     print_mes loc ("Entering " ^ fname ^ " (added to funstack)");
     Ftools.pf_s "FPAdebug" (AZ.add_show_funstack fname) az;           
     az.AZ.currentFunc <- fname;
     let sh1 = FPsh.push sh in
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
     (*
     Ftools.pf_s "FPAdebug" print_endline "--- Modified function body";
     Ftools.pf_s "FPAdebug" Kstmt.println stmtBody2;
     Ftools.pf_s "FPAdebug" print_endline "---";
      *)
     (* Main: Do funcp for the body *)       
     let r2 = funcp_stmt_sh sp_tm stmtBody2 sh1 in
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
     let r1 = FPstate.SH sh2a in
     r1
and fcall_body_fork sp_tm loc counter fname sh eeArg fprUX r =
  let pid = Unix.fork () in
  let analyzerFile = gi.GI.slacDataDir ^ "/Fpa/analyzer" in
  let filename = gi.GI.slacDataDir ^ "/tmp/" ^ fname ^ "-" ^ (string_of_int counter) in
  match pid with
  | 0 -> (* child process *)
     begin
       try
         let r1 = fcall_body sp_tm loc fname sh eeArg fprUX r in
         Ftools.write_file filename r1;
         Ftools.write_file analyzerFile az;
         exit 0
       with
         _ ->
         print_endline "Exception happens"; exit 0
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
            let r1 : FPstate.t = Ftools.read_file filename in
            r1
         | _ -> failwith ""
       with
       | _ -> failwith ""
     end
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

let println_kdata kdata =
  let (sh,structInfo,strAliases,funtable) = kdata in
  FPsh.println sh;
  GI.println_structInfo structInfo;
  GI.println_strAliases strAliases;
  GI.println_funtable funtable
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
  let r1 =
    List.fold_left
      (fun r' (topdecl,j) ->
        match topdecl with
        | KtopDecl.NA loc -> r'
        | KtopDecl.S (stmt,loc) ->
           funcp_stmt sp_tm stmt r' (* execute funcp in the topdown-mode*)
        | KtopDecl.F (tp,fname1,_,_,loc) ->
           (* print_endline @@ "Processing Func.decl: " ^ fname1; *)
           (* print_endline @@ Klocs.to_string loc; *)
           (* print_string' ","; *)
           gi.GI.funtable <- V.add fname1 (mod_name,mod_id,j) gi.GI.funtable;
           r'
      )
      r0
      (zipLst prog (List.rev (genLst (List.length prog))))
  in
  Ftools.dbg "GC" "After FPA main:" Ftools.print_gc (Gc.stat ());
  let sh1 = 
    match r1 with
    | FPstate.SH sh -> sh
    | FPstate.None -> FPsh.sh_init [] ""
  in
  (sh1,gi.GI.structs,gi.GI.straliases,gi.GI.funtable)
;;


let mainAnalysis slacDataDir fname sp_tm =

  let fpaDir = slacDataDir ^ "/Fpa" in
  Ftools.write_file (fpaDir ^ "/fpretFuncs") [];
  Ftools.write_file (fpaDir ^ "/fpretFuncsR") [];
  
  (* Path setting *)
  let fpaInitStoreHeapFp = fpaDir ^ "/initStoreHeapFp" in
  let fpaStructures = fpaDir ^ "/structures" in
  let fpaStructAliases = fpaDir ^ "/structAliases" in
  let fpaFuntable = fpaDir ^ "/funtable" in
  let fpaFundef = fpaDir ^ "/Fundef" in
  let fpaProfiles = fpaDir ^ "/Profiles" in

  (* Initalized sh *)  
  let sh0Fp = Ftools.read_file fpaInitStoreHeapFp in

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
  gi.GI.deplistFile <- slacDataDir ^ "/Fpa/deplist";
  let globalVars =
    let (s,_) = sh0Fp in
    let sFpGlobal = FPsh.fp_of s in
    List.map fst sFpGlobal
  in
  gi.GI.globalVars <- globalVars;
  Ftools.write_file gi.GI.deplistFile ([],G.empty);
  
  let (modulename,fundef) : bytes * KtopDecl.t =
    let (_,mod_id,pos) =
      try
        V.find fname gi.GI.funtable
      with
        Not_found ->
        failwith ("The toplevel function body cannot be loaded : " ^ fname)
    in
    GI.lookup_fundef gi (mod_id,pos)
  in
  
  (* Syntactical Analysis *)
  az.AZ.currentFunc <- fname;
  az.AZ.mode <- AZ.SYN;
  print_mes ~opt:"ALWAYS" ("",0) ("Syntactical Analysis of " ^ fname ^ "@" ^ modulename);    
  syntacticalAnalysis fname;

  (* Main Analysis *)
  AZ.reset AZ.FPA az;  
  print_mes ~opt:"ALWAYS" ("",0) ("Main-analysis of " ^ fname ^ " begins");

  az.AZ.currentFunc <- fname;
  az.AZ.funstack <- [fname];
  let (prms,loc,stmtBody) =
    match fundef with
    | KtopDecl.F (tp,_,prms,stmtBody,loc) -> (prms,loc,stmtBody)
    | _ -> failwith @@ "[E MemFuncp] No function definition of " ^ fname
  in
  let stmtHeadL = List.map (fun decl -> Kstmt.Decl (decl,loc)) prms in
  let loc1 = Kstmt.getloc stmtBody in
  let stmtBodyL = Kstmt.unBlock stmtBody in
  let stmtStart = Kstmt.Block (stmtHeadL @ stmtBodyL,loc1) in
  let r1 = funcp_stmt_sh sp_tm stmtStart sh0Fp in
  let fppos = az.AZ.fppos in
  let fppos1 = FpPos.subst aliases r1 fppos in
  let fppos2 = FpPos.finalize fppos1 in
  
  print_endline "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  FpPos.println fppos2;
  print_endline "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  (r1,fppos2)
;;
  
