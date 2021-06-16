
open Ftools

type ct_variable_type = VT_DATA | VT_POINTER | VT_NONE

type ct_global_type = GT_VARIABLE | GT_STRUCTURE | GT_FUNCTION | GT_NONE

(* =========================================================================== *)
(** Maps all relation of defined data types *)
let hs_types : (string , string * ct_global_type) Hashtbl.t = Hashtbl.create 0


(** Simplest form of a structure for global declarations *)
let structs : (string, (string * ct_variable_type) list) Hashtbl.t = Hashtbl.create 0  

(** Stores all global x=y and x->(y,...) data *)
let globals_eq : (string, string) Hashtbl.t = Hashtbl.create 0
let globals_ptr : (string, string list * string list) Hashtbl.t = Hashtbl.create 0

(* =========================================================================== *)



let match_key (o:string) (k:string) (v:string * ct_global_type) (a:(string * ct_global_type) option) : (string * ct_global_type) option = 
	let o, k = Bytes.trim o, Bytes.trim k in
	match a with
	| None -> if k = o then Some v else None
	| _ -> a ;;


let rec is_prefix ?(si=0) ?(pi=0) str pre = 
	try
		let s_h = String.get str si in 
		let p_h = String.get pre pi in
		if s_h = p_h then 
			is_prefix ~si:(si+1) ~pi:(pi+1) str pre
		else
			false, -1
	with
	 	_ -> 	if pi = String.length pre then
						true, si+1
					else 
						false, -1

let prefix o = 
	let pre = ["unsigned"; "signed"] in
		List.fold_left (fun (b, i) p -> if b then (b, i) else is_prefix o p) (false, -1) pre
	
let rec add_type ?t n o = 
	match prefix o with
	| (true, i) -> add_type n (Bytes.sub_string o i ((String.length o) - i)) 
	| (false, _) ->
	begin 
  	let h = Hashtbl.fold (match_key o) hs_types None in
  	match h with
  	| None -> begin
  		match t with 
  		| None -> Hashtbl.add hs_types n (o, GT_VARIABLE)
  		| Some x -> Hashtbl.add hs_types n (o, x)
  		end
  	| Some v -> Hashtbl.add hs_types n v
	end;;
	

let init () =
	add_type "int" "int";
	add_type "short" "int";
	add_type "char" "int";
	add_type "long" "int";
	add_type "long long" "int";
	add_type "float" "float";
	add_type "double" "float";	
	add_type "unsigned int" "unsigned int";
	add_type "long double" "float";;

let add_globals_eq a b = Hashtbl.add globals_eq a b 

(* =========================================================================== *)
(* =========================================================================== *)

(*
let rec get_decl_type = function
	| Cabs.JUSTBASE -> VT_DATA
	| Cabs.PARENTYPE (_, decl_type, _) -> get_decl_type decl_type
	| Cabs.ARRAY (decl_type, _, _) -> VT_POINTER
	| Cabs.PTR (_, decl_type) -> VT_POINTER
	| Cabs.PROTO _ -> VT_NONE


(**
	PROTO -> Ignore parameters; Get return type; If return type is pointer, then "name->(nil)" else "name=default_value_of_type"; Add 
*)
let rec analyze_decl_type name = function
	| Cabs.JUSTBASE -> pn "justbase"
	| Cabs.PARENTYPE (l_attr1, decl_type, l_attr2) -> pw "parenttype"; analyze_decl_type name decl_type
	| Cabs.ARRAY (decl_type, l_attr, expr) -> pw "array"; analyze_decl_type name decl_type
	| Cabs.PTR (l_attr, decl_type) -> pw "ptr"; analyze_decl_type name decl_type
	| Cabs.PROTO (decl_type, l_sname, b) -> 
			pw name; pw "="; 
			match get_decl_type decl_type with
			| VT_DATA -> pn "0"; 			add_globals_eq name "0"
			| VT_POINTER -> pn "nil"; add_globals_eq name "nil"
			| VT_FUNCTION -> pn "f"; 	add_globals_eq name "f"
			| VT_NONE -> pn "none";		add_globals_eq name "none"

let analyze_name (name, decl_type, l_attr, _) = analyze_decl_type name decl_type; () 
*)

let lop = function
	| None -> ""
	| Some x -> List.length x >> string_of_int

let get_type_spec = function
    Cabs.Tvoid -> "void"
  | Cabs.Tchar -> "char"
  | Cabs.Tbool -> "_Bool"
  | Cabs.Tshort -> "short"
  | Cabs.Tint -> "int"
  | Cabs.Tlong -> "long"
  | Cabs.Tint64 -> "__int64"
  | Cabs.Tfloat -> "float"
  | Cabs.Tdouble -> "double"
  | Cabs.Tsigned -> "signed"
  | Cabs.Tunsigned -> "unsigned"
  | Cabs.Tsizet  -> "size_t"
  | Cabs.Tnamed s ->  s 
  | Cabs.Tstruct (n, l_field, _) -> n 
  | Cabs.Tunion (n, l_field, _) -> n 
  | Cabs.Tenum (n, l_field, _) -> n
  | Cabs.TtypeofE e -> "~exp~"
  | Cabs.TtypeofT (s,d) -> "__typeof__(...)"

let get_spec_elem = function
      Cabs.SpecTypedef -> ""
    | Cabs.SpecInline -> ""
    | Cabs.SpecStorage sto -> ""
    | Cabs.SpecCV cv -> ""
    | Cabs.SpecAttr al -> ""
    | Cabs.SpecType bt -> get_type_spec bt
    | Cabs.SpecPattern name -> ""

let get_expression = function
	| Cabs.CONSTANT cst ->
      (match cst with
				Cabs.CONST_INT i -> i
      | Cabs.CONST_FLOAT r -> r
      | Cabs.CONST_CHAR c -> Escape.escape_wstring c
      | Cabs.CONST_WCHAR c -> Escape.escape_wstring c
      | Cabs.CONST_STRING s -> s
      | Cabs.CONST_WSTRING ws -> Escape.escape_wstring ws)
  | Cabs.VARIABLE name -> name
	| _ -> ""

let get_attribute (s, l_exp) = s ^ "~" ^ (concatS " " get_expression l_exp )

let rec get_fun_decl = function
    Cabs.JUSTBASE -> ""
  | Cabs.PARENTYPE (_, d, _) -> get_fun_decl d
  | Cabs.PTR (_, d) -> "*" ^ (get_fun_decl d)
  | Cabs.ARRAY (d, _, e) -> (get_fun_decl d) ^ "[" ^ (get_expression e) ^ "]"
  | Cabs.PROTO(d, args, _) -> (get_fun_decl d) ^ "(" ^ (concatS ", " get_single_name args) ^ ")"

and get_single_name (spec, (name, decl_type, l_attr, _)) = 
	let ret_type = concatS " " get_spec_elem spec in
	ret_type ^ " " ^ (get_fun_decl decl_type) 

let get_decl_type = function
	| Cabs.JUSTBASE -> "JUSTBASE"
  | Cabs.PARENTYPE (_, d, _) -> "PARENTTYPE"
  | Cabs.PTR (_, d) -> "PTR"
  | Cabs.ARRAY (d, _, e) -> "ARRAY"
  | Cabs.PROTO(d, args, _) -> "PROTO" 


let analyze_def = function
	| Cabs.TYPEDEF ((spec, l_name::_), _) -> 
		let (name, decl_type, _, _) = l_name in
		let ret_type = concatS " " get_spec_elem spec in
		let fun_string = get_fun_decl decl_type in
		let total_type = ret_type ^ " " ^ fun_string in
		if String.trim ret_type <> "" then
			begin
				add_type ~t:GT_FUNCTION name total_type; 
			end
		else
			pn (name ^ " add new struct, union, enum") 
	| _ -> ()


let print_result () =
	Hashtbl.iter (fun k (v, _) -> pw k; pw "-->"; pn v) hs_types 
(* =========================================================================== *)
		
let read_name (name, decl_type, l_attr, _) = name
	
let rec read_definition = function
	| Cabs.FUNDEF ((spec, name), block, _, _) -> p "fundef "; read_name name >> pn
	| Cabs.S_FUNDEF (_, _, func, _) -> p "s_fundef ";read_definition func
	| Cabs.S_INDDEF (_, _) -> pn "inddef"
	| Cabs.DECDEF ((spec, l_init_name), _) -> p "decdef "; List.hd l_init_name >> fst >> read_name >> pn 
	| Cabs.TYPEDEF ((spec, l_name), _) -> p "typedef "; List.iter (fun n -> p "<"; read_name n >> p; p ">") l_name; pn ""  
	| Cabs.ONLYTYPEDEF (_, _) -> pn "onlytypedef"
	| _ -> pn "<<else>>"