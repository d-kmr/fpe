open Tools;;
open Slsyntax;;
open Cprint;;
open Frontc;;

module Parser = Manualinput_parser;;
module Lexer = Manualinput_lexer;;


let rec cabfile_to_prototype cabfile =
  let (_,defL) = cabfile in
  let def = List.hd defL in
  of_definition def
  
and of_definition def =
  match def with
  | Cabs.DECDEF(init_name_group,_) -> of_init_name_group init_name_group
  | _ -> failwith ""
       
and of_init_name_group (specifier,init_name_list) =
  let rettype = List.flatten @@ List.map of_spec_elem specifier in
  match init_name_list with
  | (funcInfo,Cabs.NO_INIT)::[] ->
     let (fname,params) = of_name funcInfo in
     (rettype,fname,params)
  | _ -> failwith ""
       
and of_name funcInfo =
  match funcInfo with
  | (fname, Cabs.PROTO (decl_type,single_name_list,_),_,_) ->
     (* fname: function name (string), decl_type: parameters, attrs: ignored *)
     (*     let mytypes = of_decl_type decl_type in *)
     let params = List.map of_single_name single_name_list in
     (fname,params)
  | _ -> failwith ""
  
and of_decl_type decl_type =
  match decl_type with
  | Cabs.JUSTBASE -> []
  | Cabs.PARENTYPE (attrs1,decl_type0,attrs2) -> print_endline "Parentype"; []
  | Cabs.ARRAY (decl_type0,attrs,Cabs.CONSTANT (Cabs.CONST_INT nStr)) -> [ T.ARRAY [int_of_string nStr] ]
  | Cabs.ARRAY (decl_type0,attrs,expr) -> [ T.ARRAY [] ]
  | Cabs.PTR (attrs,decl_type0) -> T.PTR :: (of_decl_type decl_type0)
  | Cabs.PROTO (decl_type0,single_name_list,_) -> [T.PROTO]
     
and of_single_name (specifier,name) = (* ([],"x") -> *)
  let mytype0 = List.flatten @@ List.map of_spec_elem specifier in
  let (var,decl_type0,_,_) = name in
  let mytype = mytype0 @ (of_decl_type decl_type0) in
  (var,mytype)
  
and of_spec_elem spec_elem =
  match spec_elem with
  | Cabs.SpecType typeSpecifier -> of_typeSpecifier typeSpecifier
  | _ -> failwith ""

and of_typeSpecifier typeSpecifier = 
  match typeSpecifier with
  | Cabs.Tstruct (sname,_,_) -> [T.STRUCT sname]
  | Cabs.Tvoid -> []
  | Cabs.Tchar -> []
  | Cabs.Tbool -> []
  | Cabs.Tshort -> []
  | Cabs.Tint -> []
  | Cabs.Tlong -> []
  | Cabs.Tint64 -> []
  | Cabs.Tfloat -> []
  | Cabs.Tdouble -> []
  | Cabs.Tsigned -> []
  | Cabs.Tsizet -> []
  | Cabs.Tunsigned -> []
  | Cabs.Tnamed str -> []
  | Cabs.Tunion (sname,_,_) -> [T.STRUCT sname]
  | Cabs.Tenum (_,_,_) -> []
  | Cabs.TtypeofE _ -> []
  | Cabs.TtypeofT _ -> []

;;

(* parser *)
let parse str = 
  let file = Parser.main Lexer.token (Lexing.from_string str) in
  for i = 0 to List.length file - 1 do
    let funIO = List.nth file i in
    let rawfunc = funIO.MIfunctionIO.rawfunc in
    let cabfile = Frontc.parse_to_cabs_inner_from_string rawfunc in
    funIO.MIfunctionIO.func <- [cabfile_to_prototype cabfile];
  done;
  file
;;

