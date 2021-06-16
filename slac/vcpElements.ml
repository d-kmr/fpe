open Ftools
open VcpBase
module T = VcpTranslate
module V = Map.Make(Bytes)

let all_struct : (bytes * (VcpBase.Exp.t * VcpBase.Term.t) list * VcpBase.Exp.t list option) V.t ref = ref V.empty

type c_filename = bytes
type c_filepath = bytes
type ms_funcpath = bytes
type ms_filepath = bytes
type programs_t = (c_filename * c_filepath * ms_filepath * ms_funcpath) V.t
type func_t = T.Procedure.t

let get_function programs (func_name : bytes) =
  V.find func_name programs

let read_function ms_funcpath =
  let g : T.Global.t = read_file ms_funcpath in
  match g with
    T.Global.PROC (proc, _, _, _, _) ->
    proc
  | _ -> raise (StError "Wrong Refernce to FFILE @ VcpElements")
  
let get_function_details programs (func_name : bytes) : (bytes * func_t) =
  let (c_file,_,_,ms_funcpath) = get_function programs func_name in
  (c_file, read_function ms_funcpath)
;;

let get_function_ref c_file c_path ms_file ms_func = (c_file, c_path, ms_file, ms_func)

let is_a_function programs func_name =
  V.mem func_name programs

let add_to_programs func func_ref programs =
  V.add func func_ref programs
