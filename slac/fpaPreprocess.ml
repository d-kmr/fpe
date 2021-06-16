(* FPA-preprocess 
BEFORE this: 
- files for FPA are assumed to be already created and put into "fpa-directory"
THIS:
- This module reads the saved files and makes store+heap, structures, function-table.
- Then it saves these three data structures into three files.
----- until here is done in slac-gen.sh
----- after here is done in slac.native
AFTER this:
- The three files are loaded then FPA is executed
- Precond
 *)
open Tools
module V = Map.Make(Bytes)
module Kexp = Csyntax.Exp
            
module MyFpsyntax = Fpsyntax3
module MyFp = Fp3                  
module FPval = MyFpsyntax.Val
module FPsh = MyFpsyntax.StoreHeap
            
let theMain () =
  print_endline ("FPA-preprocessing (preparing for FPA main-analysis)");
  
  let argc = Array.length Sys.argv in
  if argc >= 2 then
    begin
      let slacDataDir = Sys.argv.(1) in (* <openssldir>/SlacData *)
      let fpaDir = slacDataDir ^ "/Fpa" in
      let fpaGlobalDataDir = fpaDir ^ "/GlobalData" in
      let fpaInitStoreHeapFp = fpaDir ^ "/initStoreHeapFp" in
      let fpaInitStoreHeapMod = fpaDir ^ "/initStoreHeapMod" in      
      let fpaStructures = fpaDir ^ "/structures" in
      let fpaStructAliases = fpaDir ^ "/structAliases" in
      let fpaFuntable = fpaDir ^ "/funtable" in
      let fpaFpPos = fpaDir ^ "/fpPos" in      
              
      print_endline ("Loading files in " ^ fpaDir ^ " + Preprocessing");
      
      let (sh,strV,strAliasV,funtableV) : MyFp.kdata = 
        let f kd_fold (id_name_kd : int * bytes * MyFp.kdata) =
          let loc = ("",0) in          
          let (_,name,kd0) = id_name_kd in
          let (sh0,strV0,strAliasV0,funtableV0) = kd0 in
          let (sh',strV',strAliasV',funtableV') = kd_fold in
          let sh = FPsh.union loc sh0 sh' in
          let (strV,aliasV) = MyFp.struct_union strV0 strV' in
          let funtableV = MyFp.funtable_union funtableV0 funtableV' in
          let strAliasV1 = V.union (fun alias orig1 orig2 -> Some orig1) strAliasV0 strAliasV' in
          let strAliasV = V.union (fun alias orig1 orig2 -> Some orig1) strAliasV1 aliasV in
          (sh,strV,strAliasV,funtableV)
        in
        let sh0 : FPsh.t = FPsh.sh_init [] "" in
        let kd0 : MyFp.kdata = (sh0,V.empty,V.empty,V.empty) in
        let r = Ftools.read_and_fold f kd0 fpaGlobalDataDir in
        r
      in      
      (* creating sh0_fp, which is the init sh of funcp *)
      let sh0_fp : FPsh.t =
        V.fold
          (fun strName (_,strcell) sh1 ->
            if FPsh.getRealStrName strAliasV strName <> strName then sh1 else
              let body = 
                List.fold_left
                  (fun body1 (fld,tp)->
                    match Kexp.isFpType tp, Kexp.getStructNameL tp with
                    | true,_ -> body1 @ [(fld,[FPval.Fname []])]
                    | _,[] -> body1
                    | _,strName::_ -> body1 @ [(fld,[FPval.Sname strName])]
                  )
                  []
                  strcell
              in
              let (s,h) = sh1 in
              match V.find_opt strName h with
              | None ->
                 let h1 = V.add strName body h in
                 (s,h1)
              | Some _ -> sh1
          )
          strV
          sh
      in
      
      (* creating sh0_mod, which is the init sh of modular analysis *)
      let sh0_mod : FPsh.t =
        let ((s_stack,s_retVal),h0_mod) = 
          V.fold
            (fun strName (_,strcell) sh1 ->
              if FPsh.getRealStrName strAliasV strName <> strName then sh1 else
                let body = 
                  List.fold_left
                    (fun body1 (fld,tp)->
                      match Kexp.isFpType tp, Kexp.getStructNameL tp with
                      | true,_ ->
                         let ph = FPval.toBarVarName (strName ^ "->" ^ fld) in
                         body1 @ [(fld, [FPval.Ph ph])]
                      | _,[] -> body1
                      | _,strName::_ -> body1 @ [(fld, [FPval.Sname strName])]
                    )
                    []
                    strcell
                in
                let (s,h) = sh1 in
                match V.find_opt strName h with
                | None ->
                   let h1 = V.add strName body h in
                   (s,h1)
                | Some _ -> sh1
            )
            strV
            sh
        in
        let s0_mod : FPsh.store =
          let (s_fp,retFP,retStruct) = List_mes.hd "stack_making" s_stack in
          let s_fp0 = List.map (fun (v,_) -> (v, [FPval.Ph (FPval.toBarVarName v)])) s_fp in
          let s_stack0 = [(s_fp0,retFP,retStruct)] in
          (s_stack0,s_retVal)
        in
        (s0_mod,h0_mod)
      in

      print_endline ("Saving FPA-InitStoreHeapFp to " ^ fpaInitStoreHeapFp);
      Ftools.write_file fpaInitStoreHeapFp sh0_fp;

      print_endline ("Saving FPA-InitStoreHeapMod to " ^ fpaInitStoreHeapMod);
      Ftools.write_file fpaInitStoreHeapMod sh0_mod;

      print_endline ("Saving FPA-Structures to " ^ fpaStructures);
      Ftools.write_file fpaStructures strV;

      print_endline ("Saving FPA-StructAliases to " ^ fpaStructAliases);
      Ftools.write_file fpaStructAliases strAliasV;
      
      print_endline ("Saving FPA-FuncTable to " ^ fpaFuntable);
      Ftools.write_file fpaFuntable funtableV;

      print_endline ("Saving FPA-FpPos to " ^ fpaFpPos);
      Ftools.write_file fpaFpPos [];
      
      print_endline ("FPA-preprocessing is done.");
    end
  else
    prerr_endline "Usage: fpa-preprocess <path-to-SlacData>"
;;  

theMain ()
;;
