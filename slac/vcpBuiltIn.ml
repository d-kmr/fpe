open Ftools
open VcpBase

module V = Map.Make(Bytes)
module M = Map.Make(Exp)

type t = (Term.t M.t * BExp.t list *
            Formula.ut * Term.t list)

type r = (Term.t M.t * BExp.t list *
            Formula.ut * Formula.ut)
         
let __builtins : ((t -> r) V.t) ref = ref V.empty ;;

let add_builtin nm fn =
  __builtins := V.add nm fn !__builtins

let __builtin_specs : ((Term.t list -> (Exp.attr list * Term.t list * (Term.t * (Term.t M.t * BExp.t list * Formula.ut) * (Term.t M.t * BExp.t list * Formula.ut)) list)) V.t ) ref = ref V.empty;;

let add_builtin_spec nm fn =
  __builtin_specs := V.add nm fn !__builtin_specs
;;

(*
let __builtin_object_size ((s, b, (exs,bexps,ptrs,preds), args) : t) : r =
  match args with
    p1::_::_ ->
     let rec sz pt =
       try
         let (_, data) = List.find (fun (q1,_) -> q1=pt) ptrs in
         (fun acc (_, dt) ->
           Term.op acc (sz dt) Op.ADD
         ) |->> (Term.EXP (Exp.CONST 0), data)
       with
         _ ->
         begin
           try
             let (_, data) = List.find (function ("Array",q1::_) -> q1=pt | _ -> false) preds in
             begin
               match data with
                 st::en::_ ->
                  Term.op en st Op.SUB (** This is not a precise calculation *)
               | _ ->
                  raise (StError "Invalid Array")
             end
           with
             _ ->
             Term.EXP (Exp.CONST 1)
         end
     in
     let res = sz p1 in
     let ret = Exp.VAR ("$ret", [Exp.GLOBAL]) in
     let s' = M.add ret res (M.remove ret s) in
     (s', b, (exs,bexps,ptrs,preds), ([],[],[],[]))
  | _ -> raise (StError "Insufficient Arguments")
;;

let __builtin___memset_chk ((s, b, (exs,bexps,ptrs,preds), args) : t) : r =
  match args with
    dest::ch::_::_::_ ->
     let rec set pt ptrs =
       let matched, unmatched = List.partition (fun (q1,_) -> q1=pt) ptrs in
       match matched with
         (_, data)::_ ->
          let unmatched', fields, is_ever_changed = 
            (fun (unmatched, data, is_ever_changed) (fld, dt) ->
              let is_changed, unmatched' = set dt unmatched in
              if is_changed then
                (unmatched', data @ [(fld, dt)], true)
              else
                (unmatched', data @ [(fld, ch)], is_ever_changed)
            ) |->> ((unmatched, [], false), data) in
          (is_ever_changed, unmatched @ [(pt, fields)])
       | _ ->
          false, unmatched
     in
     let _, ptrs' = set dest ptrs in
     (s, b, (exs,bexps,ptrs',preds), ([],[],[],[]))
  | _ -> raise (StError "Insufficient Arguments")
;;

let pthread_rwlock_init ((s, b, (exs,bexps,ptrs,preds), args) : t) : r =
  match args with
    lock::value::_ ->
     let res = Term.EXP (VcpVBase.new_log_var ()) in
     let ret = Exp.VAR ("$ret", [Exp.GLOBAL]) in
     let s' = M.add ret res (M.remove ret s) in
     
     (s', b, (exs,bexps,ptrs,preds), ([],[],[],[]))
  | _ -> raise (StError "Insufficient Arguments")
;;
 *)

let enbar x =
  Term.EXP (Exp.VAR (x, [Exp.BAR]))

let enfield x =
  (x, enbar x)
(**
   (1)
   functioname:
int pthread_rwlock_unlock(pthread_rwlock_t *rwlock);
output:
r:
d: true
s:
A: B[nwlock@bar -> __data -> __lock := 0]
B: AllocType(nwlock@bar,
struct {
  struct
  {
    int __lock;
    unsigned int __nr_readers;
    unsigned int __readers_wakeup;
    unsigned int __writer_wakeup;
    unsigned int __nr_readers_queued;
    unsigned int __nr_writers_queued;
    int __writer;
    int __shared;
    signed char __rwelision;
    unsigned char __pad1[7];
    unsigned long int __pad2;
    unsigned int __flags;
  } __data;
  char __size[56];
  long int __align;
},
1)
*)
let pthread_rwlock_unlock args =
  let attr = [Exp.SIMPLE (Exp.simple_size "int")] in
  let params = [Term.EXP (Exp.VAR ("rwlock", [Exp.PTR; Exp.STRUCT "pthread_rwlock_t"]))] in
  match args with
    rwlock::_ ->
     let r = Term.EXP (Exp.CONST 0) in
     let d = [] in
     let s = M.empty in

     let ptr = enbar "nwlock" in
     let __data_ptr = enbar "__data" in
     let lock_0 = ("lock", Term.EXP (Exp.CONST 0)) in
     let lock_x = ("lock", enbar "lock_x") in
     let __pad_ptr = enbar "_pad1" in
     let __data_fields = [("__nr_readers", enbar "__nr_readers");
                          enfield "__readers_wakeup";
                          enfield "__writer_wakeup";
                          enfield "__nr_readers_queued";
                          enfield "__nr_writers_queued";
                          enfield "__writer";
                          enfield "__shared";
                          enfield "__rwelision";
                          ("__pad1", __pad_ptr);
                          enfield "__pad2";
                          enfield "__flags"
                         ] in
     let __data_0 = (__data_ptr, lock_0 :: __data_fields) in
     let __data_x = (__data_ptr, lock_x :: __data_fields) in
     let __size_ptr = enbar "__size" in
     let __size_array = ("Array", __size_ptr::Term.op __size_ptr (Term.EXP (Exp.CONST 55)) Op.ADD::[]) in
     let __pad_array =  ("Array", __pad_ptr:: Term.op __pad_ptr (Term.EXP (Exp.CONST 6)) Op.ADD::[]) in
     let fields = [("__data", __data_ptr); enfield "__size"; enfield "__align"] in
     let cell = (ptr, fields) in

     let b = ([],[],[cell; __data_x],[__size_array; __pad_array]) in
     let a = ([],[],[cell; __data_0],[__size_array; __pad_array]) in
     (attr, params, [(r, (M.empty,d,b), (s,d,a))])
  | _ -> raise (StError "Insufficient Arguments")
;;

(**
size_t __builtin_object_size (const void * ptr, int type)
output:
r: -1
s:
d: true
A: emp
B: emp
 *)
let __builtin_object_size args =
  let attr = [Exp.SIMPLE (Exp.simple_size "int")] in
  let params = [Term.EXP (Exp.VAR ("ptr", [Exp.PTR])); Term.EXP (Exp.VAR ("type", [Exp.SIMPLE (Exp.simple_size "int")]))] in
  match args with
    rwlock::_ ->
     let r = Term.EXP (Exp.CONST (-1)) in
     let d = [] in
     let s = M.empty in

     let b = ([],[],[],[]) in
     let a = ([],[],[],[]) in
     (attr, params, [(r, (M.empty,d,b), (s,d,a))])
  | _ -> raise (StError "Insufficient Arguments")
;;

(**
void * __builtin___memset_chk (void *s, int c, size_t n, size_t os);
output:
r: 0
s:
d: c ne 0 and n = m * sizeof(tau)
A: Stringpart(s,s+m-1)
B: Array(s,s+m-1)

r: 0
s:
d: c = 0 and n = m * sizeof(tau)
A: Array(s,s+m-1)
B: Array(s,s+m-1)
 *)

let __builtin___memset_chk args =
  let attr = [Exp.PTR] in
  let params = [Term.EXP (Exp.VAR ("s", [Exp.PTR]));
                Term.EXP (Exp.VAR ("c", [Exp.SIMPLE (Exp.simple_size "int")]));
                Term.EXP (Exp.VAR ("n", [Exp.SIMPLE (Exp.simple_size "int")]));
                Term.EXP (Exp.VAR ("os", [Exp.SIMPLE (Exp.simple_size "int")]));
               ] in
  match args with
    Term.EXP _s::_c::_n::_os::_ ->
    let _tau, _m =
      match _n with
        Term.EXP (Exp.BINOP (Exp.SIZEOF(_) as _tau, Op.MUL, _m))
      | Term.EXP (Exp.BINOP (_m, Op.MUL, (Exp.SIZEOF(_) as _tau))) ->
         _tau, _m
      | Term.EXP (Exp.SIZEOF(_) as _tau) ->
         _tau, Exp.CONST 1
      | _ -> raise (StError "SIZEOF pattern missing")
    in
     
    let zero = Term.EXP (Exp.CONST 0) in
    let one =  Exp.CONST 1 in
    let sizeof = BExp.UNIT (_n, Op.EQ, Term.EXP (Exp.BINOP (_tau, Op.MUL, _m))) in

    let s_m_1 = Term.EXP (Exp.BINOP (_s, Op.ADD, Exp.BINOP(_m, Op.SUB, one))) in
    let arr = ("Array", [Term.EXP _s;s_m_1]) in
    let r1 = zero in
    let d1 = [BExp.UNIT (_c, Op.NE, zero); sizeof] in
    let s1 = M.empty in
    let b1 = ([],[],[],[arr]) in
    let a1 = ([],[],[],[("Stringpart", [Term.EXP _s;s_m_1])]) in

     let r2 = zero in
     let d2= [BExp.UNIT (_c, Op.EQ, zero); sizeof] in
     let s2 = M.empty in
     let b2 = ([],[],[],[arr]) in
     let a2 = ([],[],[],[arr]) in

     (attr, params, [(r1, (M.empty,d1,b1), (s1,d1,a1)); (r2, (M.empty,d2,b2), (s2,d2,a2))])
  | _ -> raise (StError "Insufficient Arguments")
;;

let _ERR_put_error args =
  let attr = [] in
  let params = [Term.EXP (Exp.VAR ("lib",  [Exp.SIMPLE (Exp.simple_size "int")]));
                Term.EXP (Exp.VAR ("func", [Exp.SIMPLE (Exp.simple_size "int")]));
                Term.EXP (Exp.VAR ("reason", [Exp.SIMPLE (Exp.simple_size "int")]));
                Term.EXP (Exp.VAR ("file", [Exp.SIMPLE (Exp.simple_size "char"); Exp.PTR]));
                Term.EXP (Exp.VAR ("len",  [Exp.SIMPLE (Exp.simple_size "int")]));
               ] in
  match args with
    _::_::_::_::_::_ ->
     let r = Term.EXP (Exp.CONST 0) in
     let d = [] in
     let s = M.empty in

     let b = ([],[],[],[]) in
     let a = ([],[],[],[]) in
     (attr, params, [(r, (M.empty,d,b), (s,d,a))])
  | _ -> raise (StError "Insufficient Arguments")
;;

let _ERR_error_string_n args =
  let attr = [] in
  let params = [Term.EXP (Exp.VAR ("e",  [Exp.SIMPLE (Exp.simple_size "long")]));
                Term.EXP (Exp.VAR ("buf", [Exp.SIMPLE (Exp.simple_size "char"); Exp.PTR]));
                Term.EXP (Exp.VAR ("len", [Exp.SIMPLE (Exp.simple_size "int")]));
                ] in
  match args with
    _::_::_::_ ->
     let r = Term.EXP (Exp.CONST 0) in
     let d = [] in
     let s = M.empty in

     let b = ([],[],[],[]) in
     let a = ([],[],[],[]) in
     (attr, params, [(r, (M.empty,d,b), (s,d,a))])
  | _ -> raise (StError "Insufficient Arguments")
;;

let _ERR_print_errors args =
  let attr = [] in
  let params = [Term.EXP (Exp.VAR ("bp",  [Exp.PTR; Exp.STRUCT "BIO"]))] in
  match args with
    _::_ ->
     let r = Term.EXP (Exp.CONST 0) in
     let d = [] in
     let s = M.empty in

     let b = ([],[],[],[]) in
     let a = ([],[],[],[]) in
     (attr, params, [(r, (M.empty,d,b), (s,d,a))])
  | _ -> raise (StError "Insufficient Arguments")
;;

let dummy params args =
  let attr = [] in
  (* let params = [] in *)
  let r = Term.EXP (Exp.CONST 0) in
  let d = [] in
  let s = M.empty in

  let b = ([],[],[],[]) in
  let a = ([],[],[],[]) in
  (attr, params, [(r, (M.empty,d,b), (s,d,a))])
;;

let rec dummy_params n =
  if n = 0 then []
  else
    (Term.EXP (Exp.VAR (string_of_int n,  [])))::dummy_params (n-1)

let init_builtins () =
  (* add_builtin "__builtin_object_size" __builtin_object_size;
  add_builtin "__builtin___memset_chk" __builtin___memset_chk;
  add_builtin "pthread_rwlock_init" pthread_rwlock_init *)

  add_builtin_spec "pthread_rwlock_unlock" pthread_rwlock_unlock;
  add_builtin_spec "__builtin_object_size" __builtin_object_size;
  add_builtin_spec "__builtin___memset_chk" __builtin___memset_chk;
  add_builtin_spec "ERR_put_error" _ERR_put_error;
  add_builtin_spec "ERR_error_string_n" _ERR_error_string_n;
  add_builtin_spec "ERR_print_errors" _ERR_print_errors;

 add_builtin_spec "__builtin_va_arg" (dummy (dummy_params 2));
 
;;

let is_builtin nm =
  V.mem nm !__builtin_specs
;;


let apply nm s b a args =
  let fn = V.find nm !__builtins in
  fn (s,b,a, args)
           
let get_spec nm args =
  let fn = V.find nm !__builtin_specs in
  fn args
