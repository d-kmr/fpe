type ptr
and symbol = ptr
and config = ptr
and context = ptr
and ast = ptr
and app = ast
and sort = ast
and func_decl = ast
and pattern = ast
and model = ptr
and literals = ptr
and constructor = ptr
and constructor_list = ptr
and solver = ptr
and goal = ptr
and tactic = ptr
and params = ptr
and probe = ptr
and stats = ptr
and ast_vector = ptr
and ast_map = ptr
and apply_result = ptr
and func_interp = ptr
and func_entry = ptr
and fixedpoint = ptr
and optimize = ptr
and param_descrs = ptr
and rcf_num = ptr
external set_internal_error_handler : ptr -> unit
  = "n_set_internal_error_handler"
external global_param_set : string -> string -> unit = "n_global_param_set"
external global_param_reset_all : unit -> unit = "n_global_param_reset_all"
external global_param_get : string -> bool * string = "n_global_param_get"
external mk_config : unit -> config = "n_mk_config"
external del_config : config -> unit = "n_del_config"
external set_param_value : config -> string -> string -> unit
  = "n_set_param_value"
external mk_context : config -> context = "n_mk_context"
external mk_context_rc : config -> context = "n_mk_context_rc"
external del_context : context -> unit = "n_del_context"
external inc_ref : context -> ast -> unit = "n_inc_ref"
external dec_ref : context -> ast -> unit = "n_dec_ref"
external update_param_value : context -> string -> string -> unit
  = "n_update_param_value"
external interrupt : context -> unit = "n_interrupt"
external mk_params : context -> params = "n_mk_params"
external params_inc_ref : context -> params -> unit = "n_params_inc_ref"
external params_dec_ref : context -> params -> unit = "n_params_dec_ref"
external params_set_bool : context -> params -> symbol -> bool -> unit
  = "n_params_set_bool"
external params_set_uint : context -> params -> symbol -> int -> unit
  = "n_params_set_uint"
external params_set_double : context -> params -> symbol -> float -> unit
  = "n_params_set_double"
external params_set_symbol : context -> params -> symbol -> symbol -> unit
  = "n_params_set_symbol"
external params_to_string : context -> params -> string
  = "n_params_to_string"
external params_validate : context -> params -> param_descrs -> unit
  = "n_params_validate"
external param_descrs_inc_ref : context -> param_descrs -> unit
  = "n_param_descrs_inc_ref"
external param_descrs_dec_ref : context -> param_descrs -> unit
  = "n_param_descrs_dec_ref"
external param_descrs_get_kind : context -> param_descrs -> symbol -> int
  = "n_param_descrs_get_kind"
external param_descrs_size : context -> param_descrs -> int
  = "n_param_descrs_size"
external param_descrs_get_name : context -> param_descrs -> int -> symbol
  = "n_param_descrs_get_name"
external param_descrs_get_documentation :
  context -> param_descrs -> symbol -> string
  = "n_param_descrs_get_documentation"
external param_descrs_to_string : context -> param_descrs -> string
  = "n_param_descrs_to_string"
external mk_int_symbol : context -> int -> symbol = "n_mk_int_symbol"
external mk_string_symbol : context -> string -> symbol
  = "n_mk_string_symbol"
external mk_uninterpreted_sort : context -> symbol -> sort
  = "n_mk_uninterpreted_sort"
external mk_bool_sort : context -> sort = "n_mk_bool_sort"
external mk_int_sort : context -> sort = "n_mk_int_sort"
external mk_real_sort : context -> sort = "n_mk_real_sort"
external mk_bv_sort : context -> int -> sort = "n_mk_bv_sort"
external mk_finite_domain_sort : context -> symbol -> int -> sort
  = "n_mk_finite_domain_sort"
external mk_array_sort : context -> sort -> sort -> sort = "n_mk_array_sort"
external mk_tuple_sort :
  context ->
  symbol -> int -> symbol list -> sort list -> sort * ptr * func_decl list
  = "n_mk_tuple_sort"
external mk_enumeration_sort :
  context ->
  symbol -> int -> symbol list -> sort * func_decl list * func_decl list
  = "n_mk_enumeration_sort"
external mk_list_sort :
  context -> symbol -> sort -> sort * ptr * ptr * ptr * ptr * ptr * ptr
  = "n_mk_list_sort"
external mk_constructor :
  context ->
  symbol ->
  symbol -> int -> symbol list -> sort list -> int list -> constructor
  = "n_mk_constructor_bytecode" "n_mk_constructor"
external del_constructor : context -> constructor -> unit
  = "n_del_constructor"
external mk_datatype :
  context -> symbol -> int -> constructor list -> sort * constructor list
  = "n_mk_datatype"
external mk_constructor_list :
  context -> int -> constructor list -> constructor_list
  = "n_mk_constructor_list"
external del_constructor_list : context -> constructor_list -> unit
  = "n_del_constructor_list"
external mk_datatypes :
  context ->
  int ->
  symbol list -> constructor_list list -> sort list * constructor_list list
  = "n_mk_datatypes"
external query_constructor :
  context -> constructor -> int -> ptr * ptr * func_decl list
  = "n_query_constructor"
external mk_func_decl :
  context -> symbol -> int -> sort list -> sort -> func_decl
  = "n_mk_func_decl"
external mk_app : context -> func_decl -> int -> ast list -> ast = "n_mk_app"
external mk_const : context -> symbol -> sort -> ast = "n_mk_const"
external mk_fresh_func_decl :
  context -> string -> int -> sort list -> sort -> func_decl
  = "n_mk_fresh_func_decl"
external mk_fresh_const : context -> string -> sort -> ast
  = "n_mk_fresh_const"
external mk_true : context -> ast = "n_mk_true"
external mk_false : context -> ast = "n_mk_false"
external mk_eq : context -> ast -> ast -> ast = "n_mk_eq"
external mk_distinct : context -> int -> ast list -> ast = "n_mk_distinct"
external mk_not : context -> ast -> ast = "n_mk_not"
external mk_ite : context -> ast -> ast -> ast -> ast = "n_mk_ite"
external mk_iff : context -> ast -> ast -> ast = "n_mk_iff"
external mk_implies : context -> ast -> ast -> ast = "n_mk_implies"
external mk_xor : context -> ast -> ast -> ast = "n_mk_xor"
external mk_and : context -> int -> ast list -> ast = "n_mk_and"
external mk_or : context -> int -> ast list -> ast = "n_mk_or"
external mk_add : context -> int -> ast list -> ast = "n_mk_add"
external mk_mul : context -> int -> ast list -> ast = "n_mk_mul"
external mk_sub : context -> int -> ast list -> ast = "n_mk_sub"
external mk_unary_minus : context -> ast -> ast = "n_mk_unary_minus"
external mk_div : context -> ast -> ast -> ast = "n_mk_div"
external mk_mod : context -> ast -> ast -> ast = "n_mk_mod"
external mk_rem : context -> ast -> ast -> ast = "n_mk_rem"
external mk_power : context -> ast -> ast -> ast = "n_mk_power"
external mk_lt : context -> ast -> ast -> ast = "n_mk_lt"
external mk_le : context -> ast -> ast -> ast = "n_mk_le"
external mk_gt : context -> ast -> ast -> ast = "n_mk_gt"
external mk_ge : context -> ast -> ast -> ast = "n_mk_ge"
external mk_int2real : context -> ast -> ast = "n_mk_int2real"
external mk_real2int : context -> ast -> ast = "n_mk_real2int"
external mk_is_int : context -> ast -> ast = "n_mk_is_int"
external mk_bvnot : context -> ast -> ast = "n_mk_bvnot"
external mk_bvredand : context -> ast -> ast = "n_mk_bvredand"
external mk_bvredor : context -> ast -> ast = "n_mk_bvredor"
external mk_bvand : context -> ast -> ast -> ast = "n_mk_bvand"
external mk_bvor : context -> ast -> ast -> ast = "n_mk_bvor"
external mk_bvxor : context -> ast -> ast -> ast = "n_mk_bvxor"
external mk_bvnand : context -> ast -> ast -> ast = "n_mk_bvnand"
external mk_bvnor : context -> ast -> ast -> ast = "n_mk_bvnor"
external mk_bvxnor : context -> ast -> ast -> ast = "n_mk_bvxnor"
external mk_bvneg : context -> ast -> ast = "n_mk_bvneg"
external mk_bvadd : context -> ast -> ast -> ast = "n_mk_bvadd"
external mk_bvsub : context -> ast -> ast -> ast = "n_mk_bvsub"
external mk_bvmul : context -> ast -> ast -> ast = "n_mk_bvmul"
external mk_bvudiv : context -> ast -> ast -> ast = "n_mk_bvudiv"
external mk_bvsdiv : context -> ast -> ast -> ast = "n_mk_bvsdiv"
external mk_bvurem : context -> ast -> ast -> ast = "n_mk_bvurem"
external mk_bvsrem : context -> ast -> ast -> ast = "n_mk_bvsrem"
external mk_bvsmod : context -> ast -> ast -> ast = "n_mk_bvsmod"
external mk_bvult : context -> ast -> ast -> ast = "n_mk_bvult"
external mk_bvslt : context -> ast -> ast -> ast = "n_mk_bvslt"
external mk_bvule : context -> ast -> ast -> ast = "n_mk_bvule"
external mk_bvsle : context -> ast -> ast -> ast = "n_mk_bvsle"
external mk_bvuge : context -> ast -> ast -> ast = "n_mk_bvuge"
external mk_bvsge : context -> ast -> ast -> ast = "n_mk_bvsge"
external mk_bvugt : context -> ast -> ast -> ast = "n_mk_bvugt"
external mk_bvsgt : context -> ast -> ast -> ast = "n_mk_bvsgt"
external mk_concat : context -> ast -> ast -> ast = "n_mk_concat"
external mk_extract : context -> int -> int -> ast -> ast = "n_mk_extract"
external mk_sign_ext : context -> int -> ast -> ast = "n_mk_sign_ext"
external mk_zero_ext : context -> int -> ast -> ast = "n_mk_zero_ext"
external mk_repeat : context -> int -> ast -> ast = "n_mk_repeat"
external mk_bvshl : context -> ast -> ast -> ast = "n_mk_bvshl"
external mk_bvlshr : context -> ast -> ast -> ast = "n_mk_bvlshr"
external mk_bvashr : context -> ast -> ast -> ast = "n_mk_bvashr"
external mk_rotate_left : context -> int -> ast -> ast = "n_mk_rotate_left"
external mk_rotate_right : context -> int -> ast -> ast = "n_mk_rotate_right"
external mk_ext_rotate_left : context -> ast -> ast -> ast
  = "n_mk_ext_rotate_left"
external mk_ext_rotate_right : context -> ast -> ast -> ast
  = "n_mk_ext_rotate_right"
external mk_int2bv : context -> int -> ast -> ast = "n_mk_int2bv"
external mk_bv2int : context -> ast -> bool -> ast = "n_mk_bv2int"
external mk_bvadd_no_overflow : context -> ast -> ast -> bool -> ast
  = "n_mk_bvadd_no_overflow"
external mk_bvadd_no_underflow : context -> ast -> ast -> ast
  = "n_mk_bvadd_no_underflow"
external mk_bvsub_no_overflow : context -> ast -> ast -> ast
  = "n_mk_bvsub_no_overflow"
external mk_bvsub_no_underflow : context -> ast -> ast -> bool -> ast
  = "n_mk_bvsub_no_underflow"
external mk_bvsdiv_no_overflow : context -> ast -> ast -> ast
  = "n_mk_bvsdiv_no_overflow"
external mk_bvneg_no_overflow : context -> ast -> ast
  = "n_mk_bvneg_no_overflow"
external mk_bvmul_no_overflow : context -> ast -> ast -> bool -> ast
  = "n_mk_bvmul_no_overflow"
external mk_bvmul_no_underflow : context -> ast -> ast -> ast
  = "n_mk_bvmul_no_underflow"
external mk_select : context -> ast -> ast -> ast = "n_mk_select"
external mk_store : context -> ast -> ast -> ast -> ast = "n_mk_store"
external mk_const_array : context -> sort -> ast -> ast = "n_mk_const_array"
external mk_map : context -> func_decl -> int -> ast list -> ast = "n_mk_map"
external mk_array_default : context -> ast -> ast = "n_mk_array_default"
external mk_set_sort : context -> sort -> sort = "n_mk_set_sort"
external mk_empty_set : context -> sort -> ast = "n_mk_empty_set"
external mk_full_set : context -> sort -> ast = "n_mk_full_set"
external mk_set_add : context -> ast -> ast -> ast = "n_mk_set_add"
external mk_set_del : context -> ast -> ast -> ast = "n_mk_set_del"
external mk_set_union : context -> int -> ast list -> ast = "n_mk_set_union"
external mk_set_intersect : context -> int -> ast list -> ast
  = "n_mk_set_intersect"
external mk_set_difference : context -> ast -> ast -> ast
  = "n_mk_set_difference"
external mk_set_complement : context -> ast -> ast = "n_mk_set_complement"
external mk_set_member : context -> ast -> ast -> ast = "n_mk_set_member"
external mk_set_subset : context -> ast -> ast -> ast = "n_mk_set_subset"
external mk_array_ext : context -> ast -> ast -> ast = "n_mk_array_ext"
external mk_numeral : context -> string -> sort -> ast = "n_mk_numeral"
external mk_real : context -> int -> int -> ast = "n_mk_real"
external mk_int : context -> int -> sort -> ast = "n_mk_int"
external mk_unsigned_int : context -> int -> sort -> ast
  = "n_mk_unsigned_int"
external mk_int64 : context -> int -> sort -> ast = "n_mk_int64"
external mk_unsigned_int64 : context -> int -> sort -> ast
  = "n_mk_unsigned_int64"
external mk_seq_sort : context -> sort -> sort = "n_mk_seq_sort"
external is_seq_sort : context -> sort -> bool = "n_is_seq_sort"
external mk_re_sort : context -> sort -> sort = "n_mk_re_sort"
external is_re_sort : context -> sort -> bool = "n_is_re_sort"
external mk_string_sort : context -> sort = "n_mk_string_sort"
external is_string_sort : context -> sort -> bool = "n_is_string_sort"
external mk_string : context -> string -> ast = "n_mk_string"
external is_string : context -> ast -> bool = "n_is_string"
external get_string : context -> ast -> string = "n_get_string"
external mk_seq_empty : context -> sort -> ast = "n_mk_seq_empty"
external mk_seq_unit : context -> ast -> ast = "n_mk_seq_unit"
external mk_seq_concat : context -> int -> ast list -> ast
  = "n_mk_seq_concat"
external mk_seq_prefix : context -> ast -> ast -> ast = "n_mk_seq_prefix"
external mk_seq_suffix : context -> ast -> ast -> ast = "n_mk_seq_suffix"
external mk_seq_contains : context -> ast -> ast -> ast = "n_mk_seq_contains"
external mk_seq_extract : context -> ast -> ast -> ast -> ast
  = "n_mk_seq_extract"
external mk_seq_replace : context -> ast -> ast -> ast -> ast
  = "n_mk_seq_replace"
external mk_seq_at : context -> ast -> ast -> ast = "n_mk_seq_at"
external mk_seq_length : context -> ast -> ast = "n_mk_seq_length"
external mk_seq_index : context -> ast -> ast -> ast -> ast
  = "n_mk_seq_index"
external mk_str_to_int : context -> ast -> ast = "n_mk_str_to_int"
external mk_int_to_str : context -> ast -> ast = "n_mk_int_to_str"
external mk_seq_to_re : context -> ast -> ast = "n_mk_seq_to_re"
external mk_seq_in_re : context -> ast -> ast -> ast = "n_mk_seq_in_re"
external mk_re_plus : context -> ast -> ast = "n_mk_re_plus"
external mk_re_star : context -> ast -> ast = "n_mk_re_star"
external mk_re_option : context -> ast -> ast = "n_mk_re_option"
external mk_re_union : context -> int -> ast list -> ast = "n_mk_re_union"
external mk_re_concat : context -> int -> ast list -> ast = "n_mk_re_concat"
external mk_re_range : context -> ast -> ast -> ast = "n_mk_re_range"
external mk_re_loop : context -> ast -> int -> int -> ast = "n_mk_re_loop"
external mk_re_intersect : context -> int -> ast list -> ast
  = "n_mk_re_intersect"
external mk_re_complement : context -> ast -> ast = "n_mk_re_complement"
external mk_re_empty : context -> sort -> ast = "n_mk_re_empty"
external mk_re_full : context -> sort -> ast = "n_mk_re_full"
external mk_pattern : context -> int -> ast list -> pattern = "n_mk_pattern"
external mk_bound : context -> int -> sort -> ast = "n_mk_bound"
external mk_forall :
  context ->
  int -> int -> pattern list -> int -> sort list -> symbol list -> ast -> ast
  = "n_mk_forall_bytecode" "n_mk_forall"
external mk_exists :
  context ->
  int -> int -> pattern list -> int -> sort list -> symbol list -> ast -> ast
  = "n_mk_exists_bytecode" "n_mk_exists"
external mk_quantifier :
  context ->
  bool ->
  int -> int -> pattern list -> int -> sort list -> symbol list -> ast -> ast
  = "n_mk_quantifier_bytecode" "n_mk_quantifier"
external mk_quantifier_ex :
  context ->
  bool ->
  int ->
  symbol ->
  symbol ->
  int ->
  pattern list ->
  int -> ast list -> int -> sort list -> symbol list -> ast -> ast
  = "n_mk_quantifier_ex_bytecode" "n_mk_quantifier_ex"
external mk_forall_const :
  context -> int -> int -> app list -> int -> pattern list -> ast -> ast
  = "n_mk_forall_const_bytecode" "n_mk_forall_const"
external mk_exists_const :
  context -> int -> int -> app list -> int -> pattern list -> ast -> ast
  = "n_mk_exists_const_bytecode" "n_mk_exists_const"
external mk_quantifier_const :
  context ->
  bool -> int -> int -> app list -> int -> pattern list -> ast -> ast
  = "n_mk_quantifier_const_bytecode" "n_mk_quantifier_const"
external mk_quantifier_const_ex :
  context ->
  bool ->
  int ->
  symbol ->
  symbol ->
  int -> app list -> int -> pattern list -> int -> ast list -> ast -> ast
  = "n_mk_quantifier_const_ex_bytecode" "n_mk_quantifier_const_ex"
external get_symbol_kind : context -> symbol -> int = "n_get_symbol_kind"
external get_symbol_int : context -> symbol -> int = "n_get_symbol_int"
external get_symbol_string : context -> symbol -> string
  = "n_get_symbol_string"
external get_sort_name : context -> sort -> symbol = "n_get_sort_name"
external get_sort_id : context -> sort -> int = "n_get_sort_id"
external sort_to_ast : context -> sort -> ast = "n_sort_to_ast"
external is_eq_sort : context -> sort -> sort -> bool = "n_is_eq_sort"
external get_sort_kind : context -> sort -> int = "n_get_sort_kind"
external get_bv_sort_size : context -> sort -> int = "n_get_bv_sort_size"
external get_finite_domain_sort_size : context -> sort -> bool * int
  = "n_get_finite_domain_sort_size"
external get_array_sort_domain : context -> sort -> sort
  = "n_get_array_sort_domain"
external get_array_sort_range : context -> sort -> sort
  = "n_get_array_sort_range"
external get_tuple_sort_mk_decl : context -> sort -> func_decl
  = "n_get_tuple_sort_mk_decl"
external get_tuple_sort_num_fields : context -> sort -> int
  = "n_get_tuple_sort_num_fields"
external get_tuple_sort_field_decl : context -> sort -> int -> func_decl
  = "n_get_tuple_sort_field_decl"
external get_datatype_sort_num_constructors : context -> sort -> int
  = "n_get_datatype_sort_num_constructors"
external get_datatype_sort_constructor : context -> sort -> int -> func_decl
  = "n_get_datatype_sort_constructor"
external get_datatype_sort_recognizer : context -> sort -> int -> func_decl
  = "n_get_datatype_sort_recognizer"
external get_datatype_sort_constructor_accessor :
  context -> sort -> int -> int -> func_decl
  = "n_get_datatype_sort_constructor_accessor"
external datatype_update_field : context -> func_decl -> ast -> ast -> ast
  = "n_datatype_update_field"
external get_relation_arity : context -> sort -> int = "n_get_relation_arity"
external get_relation_column : context -> sort -> int -> sort
  = "n_get_relation_column"
external mk_atmost : context -> int -> ast list -> int -> ast = "n_mk_atmost"
external mk_atleast : context -> int -> ast list -> int -> ast
  = "n_mk_atleast"
external mk_pble : context -> int -> ast list -> int list -> int -> ast
  = "n_mk_pble"
external mk_pbge : context -> int -> ast list -> int list -> int -> ast
  = "n_mk_pbge"
external mk_pbeq : context -> int -> ast list -> int list -> int -> ast
  = "n_mk_pbeq"
external func_decl_to_ast : context -> func_decl -> ast
  = "n_func_decl_to_ast"
external is_eq_func_decl : context -> func_decl -> func_decl -> bool
  = "n_is_eq_func_decl"
external get_func_decl_id : context -> func_decl -> int
  = "n_get_func_decl_id"
external get_decl_name : context -> func_decl -> symbol = "n_get_decl_name"
external get_decl_kind : context -> func_decl -> int = "n_get_decl_kind"
external get_domain_size : context -> func_decl -> int = "n_get_domain_size"
external get_arity : context -> func_decl -> int = "n_get_arity"
external get_domain : context -> func_decl -> int -> sort = "n_get_domain"
external get_range : context -> func_decl -> sort = "n_get_range"
external get_decl_num_parameters : context -> func_decl -> int
  = "n_get_decl_num_parameters"
external get_decl_parameter_kind : context -> func_decl -> int -> int
  = "n_get_decl_parameter_kind"
external get_decl_int_parameter : context -> func_decl -> int -> int
  = "n_get_decl_int_parameter"
external get_decl_double_parameter : context -> func_decl -> int -> float
  = "n_get_decl_double_parameter"
external get_decl_symbol_parameter : context -> func_decl -> int -> symbol
  = "n_get_decl_symbol_parameter"
external get_decl_sort_parameter : context -> func_decl -> int -> sort
  = "n_get_decl_sort_parameter"
external get_decl_ast_parameter : context -> func_decl -> int -> ast
  = "n_get_decl_ast_parameter"
external get_decl_func_decl_parameter :
  context -> func_decl -> int -> func_decl = "n_get_decl_func_decl_parameter"
external get_decl_rational_parameter : context -> func_decl -> int -> string
  = "n_get_decl_rational_parameter"
external app_to_ast : context -> app -> ast = "n_app_to_ast"
external get_app_decl : context -> app -> func_decl = "n_get_app_decl"
external get_app_num_args : context -> app -> int = "n_get_app_num_args"
external get_app_arg : context -> app -> int -> ast = "n_get_app_arg"
external is_eq_ast : context -> ast -> ast -> bool = "n_is_eq_ast"
external get_ast_id : context -> ast -> int = "n_get_ast_id"
external get_ast_hash : context -> ast -> int = "n_get_ast_hash"
external get_sort : context -> ast -> sort = "n_get_sort"
external is_well_sorted : context -> ast -> bool = "n_is_well_sorted"
external get_bool_value : context -> ast -> int = "n_get_bool_value"
external get_ast_kind : context -> ast -> int = "n_get_ast_kind"
external is_app : context -> ast -> bool = "n_is_app"
external is_numeral_ast : context -> ast -> bool = "n_is_numeral_ast"
external is_algebraic_number : context -> ast -> bool
  = "n_is_algebraic_number"
external to_app : context -> ast -> app = "n_to_app"
external to_func_decl : context -> ast -> func_decl = "n_to_func_decl"
external get_numeral_string : context -> ast -> string
  = "n_get_numeral_string"
external get_numeral_decimal_string : context -> ast -> int -> string
  = "n_get_numeral_decimal_string"
external get_numerator : context -> ast -> ast = "n_get_numerator"
external get_denominator : context -> ast -> ast = "n_get_denominator"
external get_numeral_small : context -> ast -> bool * int * int
  = "n_get_numeral_small"
external get_numeral_int : context -> ast -> bool * int = "n_get_numeral_int"
external get_numeral_uint : context -> ast -> bool * int
  = "n_get_numeral_uint"
external get_numeral_uint64 : context -> ast -> bool * int
  = "n_get_numeral_uint64"
external get_numeral_int64 : context -> ast -> bool * int
  = "n_get_numeral_int64"
external get_numeral_rational_int64 : context -> ast -> bool * int * int
  = "n_get_numeral_rational_int64"
external get_algebraic_number_lower : context -> ast -> int -> ast
  = "n_get_algebraic_number_lower"
external get_algebraic_number_upper : context -> ast -> int -> ast
  = "n_get_algebraic_number_upper"
external pattern_to_ast : context -> pattern -> ast = "n_pattern_to_ast"
external get_pattern_num_terms : context -> pattern -> int
  = "n_get_pattern_num_terms"
external get_pattern : context -> pattern -> int -> ast = "n_get_pattern"
external get_index_value : context -> ast -> int = "n_get_index_value"
external is_quantifier_forall : context -> ast -> bool
  = "n_is_quantifier_forall"
external get_quantifier_weight : context -> ast -> int
  = "n_get_quantifier_weight"
external get_quantifier_num_patterns : context -> ast -> int
  = "n_get_quantifier_num_patterns"
external get_quantifier_pattern_ast : context -> ast -> int -> pattern
  = "n_get_quantifier_pattern_ast"
external get_quantifier_num_no_patterns : context -> ast -> int
  = "n_get_quantifier_num_no_patterns"
external get_quantifier_no_pattern_ast : context -> ast -> int -> ast
  = "n_get_quantifier_no_pattern_ast"
external get_quantifier_num_bound : context -> ast -> int
  = "n_get_quantifier_num_bound"
external get_quantifier_bound_name : context -> ast -> int -> symbol
  = "n_get_quantifier_bound_name"
external get_quantifier_bound_sort : context -> ast -> int -> sort
  = "n_get_quantifier_bound_sort"
external get_quantifier_body : context -> ast -> ast
  = "n_get_quantifier_body"
external simplify : context -> ast -> ast = "n_simplify"
external simplify_ex : context -> ast -> params -> ast = "n_simplify_ex"
external simplify_get_help : context -> string = "n_simplify_get_help"
external simplify_get_param_descrs : context -> param_descrs
  = "n_simplify_get_param_descrs"
external update_term : context -> ast -> int -> ast list -> ast
  = "n_update_term"
external substitute : context -> ast -> int -> ast list -> ast list -> ast
  = "n_substitute"
external substitute_vars : context -> ast -> int -> ast list -> ast
  = "n_substitute_vars"
external translate : context -> ast -> context -> ast = "n_translate"
external model_inc_ref : context -> model -> unit = "n_model_inc_ref"
external model_dec_ref : context -> model -> unit = "n_model_dec_ref"
external model_eval : context -> model -> ast -> bool -> bool * ptr
  = "n_model_eval"
external model_get_const_interp : context -> model -> func_decl -> ast
  = "n_model_get_const_interp"
external model_has_interp : context -> model -> func_decl -> bool
  = "n_model_has_interp"
external model_get_func_interp : context -> model -> func_decl -> func_interp
  = "n_model_get_func_interp"
external model_get_num_consts : context -> model -> int
  = "n_model_get_num_consts"
external model_get_const_decl : context -> model -> int -> func_decl
  = "n_model_get_const_decl"
external model_get_num_funcs : context -> model -> int
  = "n_model_get_num_funcs"
external model_get_func_decl : context -> model -> int -> func_decl
  = "n_model_get_func_decl"
external model_get_num_sorts : context -> model -> int
  = "n_model_get_num_sorts"
external model_get_sort : context -> model -> int -> sort
  = "n_model_get_sort"
external model_get_sort_universe : context -> model -> sort -> ast_vector
  = "n_model_get_sort_universe"
external is_as_array : context -> ast -> bool = "n_is_as_array"
external get_as_array_func_decl : context -> ast -> func_decl
  = "n_get_as_array_func_decl"
external func_interp_inc_ref : context -> func_interp -> unit
  = "n_func_interp_inc_ref"
external func_interp_dec_ref : context -> func_interp -> unit
  = "n_func_interp_dec_ref"
external func_interp_get_num_entries : context -> func_interp -> int
  = "n_func_interp_get_num_entries"
external func_interp_get_entry : context -> func_interp -> int -> func_entry
  = "n_func_interp_get_entry"
external func_interp_get_else : context -> func_interp -> ast
  = "n_func_interp_get_else"
external func_interp_get_arity : context -> func_interp -> int
  = "n_func_interp_get_arity"
external func_entry_inc_ref : context -> func_entry -> unit
  = "n_func_entry_inc_ref"
external func_entry_dec_ref : context -> func_entry -> unit
  = "n_func_entry_dec_ref"
external func_entry_get_value : context -> func_entry -> ast
  = "n_func_entry_get_value"
external func_entry_get_num_args : context -> func_entry -> int
  = "n_func_entry_get_num_args"
external func_entry_get_arg : context -> func_entry -> int -> ast
  = "n_func_entry_get_arg"
external open_log : string -> int = "n_open_log"
external append_log : string -> unit = "n_append_log"
external close_log : unit -> unit = "n_close_log"
external toggle_warning_messages : bool -> unit = "n_toggle_warning_messages"
external set_ast_print_mode : context -> int -> unit = "n_set_ast_print_mode"
external ast_to_string : context -> ast -> string = "n_ast_to_string"
external pattern_to_string : context -> pattern -> string
  = "n_pattern_to_string"
external sort_to_string : context -> sort -> string = "n_sort_to_string"
external func_decl_to_string : context -> func_decl -> string
  = "n_func_decl_to_string"
external model_to_string : context -> model -> string = "n_model_to_string"
external benchmark_to_smtlib_string :
  context ->
  string -> string -> string -> string -> int -> ast list -> ast -> string
  = "n_benchmark_to_smtlib_string_bytecode" "n_benchmark_to_smtlib_string"
external parse_smtlib2_string :
  context ->
  string ->
  int ->
  symbol list -> sort list -> int -> symbol list -> func_decl list -> ast
  = "n_parse_smtlib2_string_bytecode" "n_parse_smtlib2_string"
external parse_smtlib2_file :
  context ->
  string ->
  int ->
  symbol list -> sort list -> int -> symbol list -> func_decl list -> ast
  = "n_parse_smtlib2_file_bytecode" "n_parse_smtlib2_file"
external parse_smtlib_string :
  context ->
  string ->
  int ->
  symbol list -> sort list -> int -> symbol list -> func_decl list -> unit
  = "n_parse_smtlib_string_bytecode" "n_parse_smtlib_string"
external parse_smtlib_file :
  context ->
  string ->
  int ->
  symbol list -> sort list -> int -> symbol list -> func_decl list -> unit
  = "n_parse_smtlib_file_bytecode" "n_parse_smtlib_file"
external get_smtlib_num_formulas : context -> int
  = "n_get_smtlib_num_formulas"
external get_smtlib_formula : context -> int -> ast = "n_get_smtlib_formula"
external get_smtlib_num_assumptions : context -> int
  = "n_get_smtlib_num_assumptions"
external get_smtlib_assumption : context -> int -> ast
  = "n_get_smtlib_assumption"
external get_smtlib_num_decls : context -> int = "n_get_smtlib_num_decls"
external get_smtlib_decl : context -> int -> func_decl = "n_get_smtlib_decl"
external get_smtlib_num_sorts : context -> int = "n_get_smtlib_num_sorts"
external get_smtlib_sort : context -> int -> sort = "n_get_smtlib_sort"
external get_smtlib_error : context -> string = "n_get_smtlib_error"
external get_error_code : context -> int = "n_get_error_code"
external set_error : context -> int -> unit = "n_set_error"
external get_error_msg : context -> int -> string = "n_get_error_msg"
external get_version : unit -> int * int * int * int = "n_get_version"
external get_full_version : unit -> string = "n_get_full_version"
external enable_trace : string -> unit = "n_enable_trace"
external disable_trace : string -> unit = "n_disable_trace"
external reset_memory : unit -> unit = "n_reset_memory"
external finalize_memory : unit -> unit = "n_finalize_memory"
external mk_goal : context -> bool -> bool -> bool -> goal = "n_mk_goal"
external goal_inc_ref : context -> goal -> unit = "n_goal_inc_ref"
external goal_dec_ref : context -> goal -> unit = "n_goal_dec_ref"
external goal_precision : context -> goal -> int = "n_goal_precision"
external goal_assert : context -> goal -> ast -> unit = "n_goal_assert"
external goal_inconsistent : context -> goal -> bool = "n_goal_inconsistent"
external goal_depth : context -> goal -> int = "n_goal_depth"
external goal_reset : context -> goal -> unit = "n_goal_reset"
external goal_size : context -> goal -> int = "n_goal_size"
external goal_formula : context -> goal -> int -> ast = "n_goal_formula"
external goal_num_exprs : context -> goal -> int = "n_goal_num_exprs"
external goal_is_decided_sat : context -> goal -> bool
  = "n_goal_is_decided_sat"
external goal_is_decided_unsat : context -> goal -> bool
  = "n_goal_is_decided_unsat"
external goal_translate : context -> goal -> context -> goal
  = "n_goal_translate"
external goal_to_string : context -> goal -> string = "n_goal_to_string"
external mk_tactic : context -> string -> tactic = "n_mk_tactic"
external tactic_inc_ref : context -> tactic -> unit = "n_tactic_inc_ref"
external tactic_dec_ref : context -> tactic -> unit = "n_tactic_dec_ref"
external mk_probe : context -> string -> probe = "n_mk_probe"
external probe_inc_ref : context -> probe -> unit = "n_probe_inc_ref"
external probe_dec_ref : context -> probe -> unit = "n_probe_dec_ref"
external tactic_and_then : context -> tactic -> tactic -> tactic
  = "n_tactic_and_then"
external tactic_or_else : context -> tactic -> tactic -> tactic
  = "n_tactic_or_else"
external tactic_par_or : context -> int -> tactic list -> tactic
  = "n_tactic_par_or"
external tactic_par_and_then : context -> tactic -> tactic -> tactic
  = "n_tactic_par_and_then"
external tactic_try_for : context -> tactic -> int -> tactic
  = "n_tactic_try_for"
external tactic_when : context -> probe -> tactic -> tactic = "n_tactic_when"
external tactic_cond : context -> probe -> tactic -> tactic -> tactic
  = "n_tactic_cond"
external tactic_repeat : context -> tactic -> int -> tactic
  = "n_tactic_repeat"
external tactic_skip : context -> tactic = "n_tactic_skip"
external tactic_fail : context -> tactic = "n_tactic_fail"
external tactic_fail_if : context -> probe -> tactic = "n_tactic_fail_if"
external tactic_fail_if_not_decided : context -> tactic
  = "n_tactic_fail_if_not_decided"
external tactic_using_params : context -> tactic -> params -> tactic
  = "n_tactic_using_params"
external probe_const : context -> float -> probe = "n_probe_const"
external probe_lt : context -> probe -> probe -> probe = "n_probe_lt"
external probe_gt : context -> probe -> probe -> probe = "n_probe_gt"
external probe_le : context -> probe -> probe -> probe = "n_probe_le"
external probe_ge : context -> probe -> probe -> probe = "n_probe_ge"
external probe_eq : context -> probe -> probe -> probe = "n_probe_eq"
external probe_and : context -> probe -> probe -> probe = "n_probe_and"
external probe_or : context -> probe -> probe -> probe = "n_probe_or"
external probe_not : context -> probe -> probe = "n_probe_not"
external get_num_tactics : context -> int = "n_get_num_tactics"
external get_tactic_name : context -> int -> string = "n_get_tactic_name"
external get_num_probes : context -> int = "n_get_num_probes"
external get_probe_name : context -> int -> string = "n_get_probe_name"
external tactic_get_help : context -> tactic -> string = "n_tactic_get_help"
external tactic_get_param_descrs : context -> tactic -> param_descrs
  = "n_tactic_get_param_descrs"
external tactic_get_descr : context -> string -> string
  = "n_tactic_get_descr"
external probe_get_descr : context -> string -> string = "n_probe_get_descr"
external probe_apply : context -> probe -> goal -> float = "n_probe_apply"
external tactic_apply : context -> tactic -> goal -> apply_result
  = "n_tactic_apply"
external tactic_apply_ex :
  context -> tactic -> goal -> params -> apply_result = "n_tactic_apply_ex"
external apply_result_inc_ref : context -> apply_result -> unit
  = "n_apply_result_inc_ref"
external apply_result_dec_ref : context -> apply_result -> unit
  = "n_apply_result_dec_ref"
external apply_result_to_string : context -> apply_result -> string
  = "n_apply_result_to_string"
external apply_result_get_num_subgoals : context -> apply_result -> int
  = "n_apply_result_get_num_subgoals"
external apply_result_get_subgoal : context -> apply_result -> int -> goal
  = "n_apply_result_get_subgoal"
external apply_result_convert_model :
  context -> apply_result -> int -> model -> model
  = "n_apply_result_convert_model"
external mk_solver : context -> solver = "n_mk_solver"
external mk_simple_solver : context -> solver = "n_mk_simple_solver"
external mk_solver_for_logic : context -> symbol -> solver
  = "n_mk_solver_for_logic"
external mk_solver_from_tactic : context -> tactic -> solver
  = "n_mk_solver_from_tactic"
external solver_translate : context -> solver -> context -> solver
  = "n_solver_translate"
external solver_get_help : context -> solver -> string = "n_solver_get_help"
external solver_get_param_descrs : context -> solver -> param_descrs
  = "n_solver_get_param_descrs"
external solver_set_params : context -> solver -> params -> unit
  = "n_solver_set_params"
external solver_inc_ref : context -> solver -> unit = "n_solver_inc_ref"
external solver_dec_ref : context -> solver -> unit = "n_solver_dec_ref"
external solver_push : context -> solver -> unit = "n_solver_push"
external solver_pop : context -> solver -> int -> unit = "n_solver_pop"
external solver_reset : context -> solver -> unit = "n_solver_reset"
external solver_get_num_scopes : context -> solver -> int
  = "n_solver_get_num_scopes"
external solver_assert : context -> solver -> ast -> unit = "n_solver_assert"
external solver_assert_and_track : context -> solver -> ast -> ast -> unit
  = "n_solver_assert_and_track"
external solver_get_assertions : context -> solver -> ast_vector
  = "n_solver_get_assertions"
external solver_check : context -> solver -> int = "n_solver_check"
external solver_check_assumptions :
  context -> solver -> int -> ast list -> int = "n_solver_check_assumptions"
external get_implied_equalities :
  context -> solver -> int -> ast list -> int * int list
  = "n_get_implied_equalities"
external solver_get_consequences :
  context -> solver -> ast_vector -> ast_vector -> ast_vector -> int
  = "n_solver_get_consequences"
external solver_get_model : context -> solver -> model = "n_solver_get_model"
external solver_get_proof : context -> solver -> ast = "n_solver_get_proof"
external solver_get_unsat_core : context -> solver -> ast_vector
  = "n_solver_get_unsat_core"
external solver_get_reason_unknown : context -> solver -> string
  = "n_solver_get_reason_unknown"
external solver_get_statistics : context -> solver -> stats
  = "n_solver_get_statistics"
external solver_to_string : context -> solver -> string
  = "n_solver_to_string"
external stats_to_string : context -> stats -> string = "n_stats_to_string"
external stats_inc_ref : context -> stats -> unit = "n_stats_inc_ref"
external stats_dec_ref : context -> stats -> unit = "n_stats_dec_ref"
external stats_size : context -> stats -> int = "n_stats_size"
external stats_get_key : context -> stats -> int -> string
  = "n_stats_get_key"
external stats_is_uint : context -> stats -> int -> bool = "n_stats_is_uint"
external stats_is_double : context -> stats -> int -> bool
  = "n_stats_is_double"
external stats_get_uint_value : context -> stats -> int -> int
  = "n_stats_get_uint_value"
external stats_get_double_value : context -> stats -> int -> float
  = "n_stats_get_double_value"
external get_estimated_alloc_size : unit -> int
  = "n_get_estimated_alloc_size"
external mk_ast_vector : context -> ast_vector = "n_mk_ast_vector"
external ast_vector_inc_ref : context -> ast_vector -> unit
  = "n_ast_vector_inc_ref"
external ast_vector_dec_ref : context -> ast_vector -> unit
  = "n_ast_vector_dec_ref"
external ast_vector_size : context -> ast_vector -> int = "n_ast_vector_size"
external ast_vector_get : context -> ast_vector -> int -> ast
  = "n_ast_vector_get"
external ast_vector_set : context -> ast_vector -> int -> ast -> unit
  = "n_ast_vector_set"
external ast_vector_resize : context -> ast_vector -> int -> unit
  = "n_ast_vector_resize"
external ast_vector_push : context -> ast_vector -> ast -> unit
  = "n_ast_vector_push"
external ast_vector_translate :
  context -> ast_vector -> context -> ast_vector = "n_ast_vector_translate"
external ast_vector_to_string : context -> ast_vector -> string
  = "n_ast_vector_to_string"
external mk_ast_map : context -> ast_map = "n_mk_ast_map"
external ast_map_inc_ref : context -> ast_map -> unit = "n_ast_map_inc_ref"
external ast_map_dec_ref : context -> ast_map -> unit = "n_ast_map_dec_ref"
external ast_map_contains : context -> ast_map -> ast -> bool
  = "n_ast_map_contains"
external ast_map_find : context -> ast_map -> ast -> ast = "n_ast_map_find"
external ast_map_insert : context -> ast_map -> ast -> ast -> unit
  = "n_ast_map_insert"
external ast_map_erase : context -> ast_map -> ast -> unit
  = "n_ast_map_erase"
external ast_map_reset : context -> ast_map -> unit = "n_ast_map_reset"
external ast_map_size : context -> ast_map -> int = "n_ast_map_size"
external ast_map_keys : context -> ast_map -> ast_vector = "n_ast_map_keys"
external ast_map_to_string : context -> ast_map -> string
  = "n_ast_map_to_string"
external algebraic_is_value : context -> ast -> bool = "n_algebraic_is_value"
external algebraic_is_pos : context -> ast -> bool = "n_algebraic_is_pos"
external algebraic_is_neg : context -> ast -> bool = "n_algebraic_is_neg"
external algebraic_is_zero : context -> ast -> bool = "n_algebraic_is_zero"
external algebraic_sign : context -> ast -> int = "n_algebraic_sign"
external algebraic_add : context -> ast -> ast -> ast = "n_algebraic_add"
external algebraic_sub : context -> ast -> ast -> ast = "n_algebraic_sub"
external algebraic_mul : context -> ast -> ast -> ast = "n_algebraic_mul"
external algebraic_div : context -> ast -> ast -> ast = "n_algebraic_div"
external algebraic_root : context -> ast -> int -> ast = "n_algebraic_root"
external algebraic_power : context -> ast -> int -> ast = "n_algebraic_power"
external algebraic_lt : context -> ast -> ast -> bool = "n_algebraic_lt"
external algebraic_gt : context -> ast -> ast -> bool = "n_algebraic_gt"
external algebraic_le : context -> ast -> ast -> bool = "n_algebraic_le"
external algebraic_ge : context -> ast -> ast -> bool = "n_algebraic_ge"
external algebraic_eq : context -> ast -> ast -> bool = "n_algebraic_eq"
external algebraic_neq : context -> ast -> ast -> bool = "n_algebraic_neq"
external algebraic_roots : context -> ast -> int -> ast list -> ast_vector
  = "n_algebraic_roots"
external algebraic_eval : context -> ast -> int -> ast list -> int
  = "n_algebraic_eval"
external polynomial_subresultants :
  context -> ast -> ast -> ast -> ast_vector = "n_polynomial_subresultants"
external rcf_del : context -> rcf_num -> unit = "n_rcf_del"
external rcf_mk_rational : context -> string -> rcf_num = "n_rcf_mk_rational"
external rcf_mk_small_int : context -> int -> rcf_num = "n_rcf_mk_small_int"
external rcf_mk_pi : context -> rcf_num = "n_rcf_mk_pi"
external rcf_mk_e : context -> rcf_num = "n_rcf_mk_e"
external rcf_mk_infinitesimal : context -> rcf_num = "n_rcf_mk_infinitesimal"
external rcf_mk_roots : context -> int -> rcf_num list -> int * rcf_num list
  = "n_rcf_mk_roots"
external rcf_add : context -> rcf_num -> rcf_num -> rcf_num = "n_rcf_add"
external rcf_sub : context -> rcf_num -> rcf_num -> rcf_num = "n_rcf_sub"
external rcf_mul : context -> rcf_num -> rcf_num -> rcf_num = "n_rcf_mul"
external rcf_div : context -> rcf_num -> rcf_num -> rcf_num = "n_rcf_div"
external rcf_neg : context -> rcf_num -> rcf_num = "n_rcf_neg"
external rcf_inv : context -> rcf_num -> rcf_num = "n_rcf_inv"
external rcf_power : context -> rcf_num -> int -> rcf_num = "n_rcf_power"
external rcf_lt : context -> rcf_num -> rcf_num -> bool = "n_rcf_lt"
external rcf_gt : context -> rcf_num -> rcf_num -> bool = "n_rcf_gt"
external rcf_le : context -> rcf_num -> rcf_num -> bool = "n_rcf_le"
external rcf_ge : context -> rcf_num -> rcf_num -> bool = "n_rcf_ge"
external rcf_eq : context -> rcf_num -> rcf_num -> bool = "n_rcf_eq"
external rcf_neq : context -> rcf_num -> rcf_num -> bool = "n_rcf_neq"
external rcf_num_to_string : context -> rcf_num -> bool -> bool -> string
  = "n_rcf_num_to_string"
external rcf_num_to_decimal_string : context -> rcf_num -> int -> string
  = "n_rcf_num_to_decimal_string"
external rcf_get_numerator_denominator : context -> rcf_num -> ptr * ptr
  = "n_rcf_get_numerator_denominator"
external mk_fixedpoint : context -> fixedpoint = "n_mk_fixedpoint"
external fixedpoint_inc_ref : context -> fixedpoint -> unit
  = "n_fixedpoint_inc_ref"
external fixedpoint_dec_ref : context -> fixedpoint -> unit
  = "n_fixedpoint_dec_ref"
external fixedpoint_add_rule : context -> fixedpoint -> ast -> symbol -> unit
  = "n_fixedpoint_add_rule"
external fixedpoint_add_fact :
  context -> fixedpoint -> func_decl -> int -> int list -> unit
  = "n_fixedpoint_add_fact"
external fixedpoint_assert : context -> fixedpoint -> ast -> unit
  = "n_fixedpoint_assert"
external fixedpoint_query : context -> fixedpoint -> ast -> int
  = "n_fixedpoint_query"
external fixedpoint_query_relations :
  context -> fixedpoint -> int -> func_decl list -> int
  = "n_fixedpoint_query_relations"
external fixedpoint_get_answer : context -> fixedpoint -> ast
  = "n_fixedpoint_get_answer"
external fixedpoint_get_reason_unknown : context -> fixedpoint -> string
  = "n_fixedpoint_get_reason_unknown"
external fixedpoint_update_rule :
  context -> fixedpoint -> ast -> symbol -> unit = "n_fixedpoint_update_rule"
external fixedpoint_get_num_levels :
  context -> fixedpoint -> func_decl -> int = "n_fixedpoint_get_num_levels"
external fixedpoint_get_cover_delta :
  context -> fixedpoint -> int -> func_decl -> ast
  = "n_fixedpoint_get_cover_delta"
external fixedpoint_add_cover :
  context -> fixedpoint -> int -> func_decl -> ast -> unit
  = "n_fixedpoint_add_cover"
external fixedpoint_get_statistics : context -> fixedpoint -> stats
  = "n_fixedpoint_get_statistics"
external fixedpoint_register_relation :
  context -> fixedpoint -> func_decl -> unit
  = "n_fixedpoint_register_relation"
external fixedpoint_set_predicate_representation :
  context -> fixedpoint -> func_decl -> int -> symbol list -> unit
  = "n_fixedpoint_set_predicate_representation"
external fixedpoint_get_rules : context -> fixedpoint -> ast_vector
  = "n_fixedpoint_get_rules"
external fixedpoint_get_assertions : context -> fixedpoint -> ast_vector
  = "n_fixedpoint_get_assertions"
external fixedpoint_set_params : context -> fixedpoint -> params -> unit
  = "n_fixedpoint_set_params"
external fixedpoint_get_help : context -> fixedpoint -> string
  = "n_fixedpoint_get_help"
external fixedpoint_get_param_descrs : context -> fixedpoint -> param_descrs
  = "n_fixedpoint_get_param_descrs"
external fixedpoint_to_string :
  context -> fixedpoint -> int -> ast list -> string
  = "n_fixedpoint_to_string"
external fixedpoint_from_string :
  context -> fixedpoint -> string -> ast_vector = "n_fixedpoint_from_string"
external fixedpoint_from_file : context -> fixedpoint -> string -> ast_vector
  = "n_fixedpoint_from_file"
external fixedpoint_push : context -> fixedpoint -> unit
  = "n_fixedpoint_push"
external fixedpoint_pop : context -> fixedpoint -> unit = "n_fixedpoint_pop"
external mk_optimize : context -> optimize = "n_mk_optimize"
external optimize_inc_ref : context -> optimize -> unit
  = "n_optimize_inc_ref"
external optimize_dec_ref : context -> optimize -> unit
  = "n_optimize_dec_ref"
external optimize_assert : context -> optimize -> ast -> unit
  = "n_optimize_assert"
external optimize_assert_soft :
  context -> optimize -> ast -> string -> symbol -> int
  = "n_optimize_assert_soft"
external optimize_maximize : context -> optimize -> ast -> int
  = "n_optimize_maximize"
external optimize_minimize : context -> optimize -> ast -> int
  = "n_optimize_minimize"
external optimize_push : context -> optimize -> unit = "n_optimize_push"
external optimize_pop : context -> optimize -> unit = "n_optimize_pop"
external optimize_check : context -> optimize -> int = "n_optimize_check"
external optimize_get_reason_unknown : context -> optimize -> string
  = "n_optimize_get_reason_unknown"
external optimize_get_model : context -> optimize -> model
  = "n_optimize_get_model"
external optimize_set_params : context -> optimize -> params -> unit
  = "n_optimize_set_params"
external optimize_get_param_descrs : context -> optimize -> param_descrs
  = "n_optimize_get_param_descrs"
external optimize_get_lower : context -> optimize -> int -> ast
  = "n_optimize_get_lower"
external optimize_get_upper : context -> optimize -> int -> ast
  = "n_optimize_get_upper"
external optimize_get_lower_as_vector :
  context -> optimize -> int -> ast_vector = "n_optimize_get_lower_as_vector"
external optimize_get_upper_as_vector :
  context -> optimize -> int -> ast_vector = "n_optimize_get_upper_as_vector"
external optimize_to_string : context -> optimize -> string
  = "n_optimize_to_string"
external optimize_from_string : context -> optimize -> string -> unit
  = "n_optimize_from_string"
external optimize_from_file : context -> optimize -> string -> unit
  = "n_optimize_from_file"
external optimize_get_help : context -> optimize -> string
  = "n_optimize_get_help"
external optimize_get_statistics : context -> optimize -> stats
  = "n_optimize_get_statistics"
external optimize_get_assertions : context -> optimize -> ast_vector
  = "n_optimize_get_assertions"
external optimize_get_objectives : context -> optimize -> ast_vector
  = "n_optimize_get_objectives"
external mk_interpolant : context -> ast -> ast = "n_mk_interpolant"
external mk_interpolation_context : config -> context
  = "n_mk_interpolation_context"
external get_interpolant : context -> ast -> ast -> params -> ast_vector
  = "n_get_interpolant"
external compute_interpolant : context -> ast -> params -> int * ptr * ptr
  = "n_compute_interpolant"
external interpolation_profile : context -> string
  = "n_interpolation_profile"
external read_interpolation_problem :
  context ->
  string -> int * int * ast list * int list * string * int * ast list
  = "n_read_interpolation_problem"
external check_interpolant :
  context ->
  int -> ast list -> int list -> ast list -> int -> ast list -> int * string
  = "n_check_interpolant_bytecode" "n_check_interpolant"
external write_interpolation_problem :
  context -> int -> ast list -> int list -> string -> int -> ast list -> unit
  = "n_write_interpolation_problem_bytecode" "n_write_interpolation_problem"
external mk_fpa_rounding_mode_sort : context -> sort
  = "n_mk_fpa_rounding_mode_sort"
external mk_fpa_round_nearest_ties_to_even : context -> ast
  = "n_mk_fpa_round_nearest_ties_to_even"
external mk_fpa_rne : context -> ast = "n_mk_fpa_rne"
external mk_fpa_round_nearest_ties_to_away : context -> ast
  = "n_mk_fpa_round_nearest_ties_to_away"
external mk_fpa_rna : context -> ast = "n_mk_fpa_rna"
external mk_fpa_round_toward_positive : context -> ast
  = "n_mk_fpa_round_toward_positive"
external mk_fpa_rtp : context -> ast = "n_mk_fpa_rtp"
external mk_fpa_round_toward_negative : context -> ast
  = "n_mk_fpa_round_toward_negative"
external mk_fpa_rtn : context -> ast = "n_mk_fpa_rtn"
external mk_fpa_round_toward_zero : context -> ast
  = "n_mk_fpa_round_toward_zero"
external mk_fpa_rtz : context -> ast = "n_mk_fpa_rtz"
external mk_fpa_sort : context -> int -> int -> sort = "n_mk_fpa_sort"
external mk_fpa_sort_half : context -> sort = "n_mk_fpa_sort_half"
external mk_fpa_sort_16 : context -> sort = "n_mk_fpa_sort_16"
external mk_fpa_sort_single : context -> sort = "n_mk_fpa_sort_single"
external mk_fpa_sort_32 : context -> sort = "n_mk_fpa_sort_32"
external mk_fpa_sort_double : context -> sort = "n_mk_fpa_sort_double"
external mk_fpa_sort_64 : context -> sort = "n_mk_fpa_sort_64"
external mk_fpa_sort_quadruple : context -> sort = "n_mk_fpa_sort_quadruple"
external mk_fpa_sort_128 : context -> sort = "n_mk_fpa_sort_128"
external mk_fpa_nan : context -> sort -> ast = "n_mk_fpa_nan"
external mk_fpa_inf : context -> sort -> bool -> ast = "n_mk_fpa_inf"
external mk_fpa_zero : context -> sort -> bool -> ast = "n_mk_fpa_zero"
external mk_fpa_fp : context -> ast -> ast -> ast -> ast = "n_mk_fpa_fp"
external mk_fpa_numeral_float : context -> float -> sort -> ast
  = "n_mk_fpa_numeral_float"
external mk_fpa_numeral_double : context -> float -> sort -> ast
  = "n_mk_fpa_numeral_double"
external mk_fpa_numeral_int : context -> int -> sort -> ast
  = "n_mk_fpa_numeral_int"
external mk_fpa_numeral_int_uint :
  context -> bool -> int -> int -> sort -> ast = "n_mk_fpa_numeral_int_uint"
external mk_fpa_numeral_int64_uint64 :
  context -> bool -> int -> int -> sort -> ast
  = "n_mk_fpa_numeral_int64_uint64"
external mk_fpa_abs : context -> ast -> ast = "n_mk_fpa_abs"
external mk_fpa_neg : context -> ast -> ast = "n_mk_fpa_neg"
external mk_fpa_add : context -> ast -> ast -> ast -> ast = "n_mk_fpa_add"
external mk_fpa_sub : context -> ast -> ast -> ast -> ast = "n_mk_fpa_sub"
external mk_fpa_mul : context -> ast -> ast -> ast -> ast = "n_mk_fpa_mul"
external mk_fpa_div : context -> ast -> ast -> ast -> ast = "n_mk_fpa_div"
external mk_fpa_fma : context -> ast -> ast -> ast -> ast -> ast
  = "n_mk_fpa_fma"
external mk_fpa_sqrt : context -> ast -> ast -> ast = "n_mk_fpa_sqrt"
external mk_fpa_rem : context -> ast -> ast -> ast = "n_mk_fpa_rem"
external mk_fpa_round_to_integral : context -> ast -> ast -> ast
  = "n_mk_fpa_round_to_integral"
external mk_fpa_min : context -> ast -> ast -> ast = "n_mk_fpa_min"
external mk_fpa_max : context -> ast -> ast -> ast = "n_mk_fpa_max"
external mk_fpa_leq : context -> ast -> ast -> ast = "n_mk_fpa_leq"
external mk_fpa_lt : context -> ast -> ast -> ast = "n_mk_fpa_lt"
external mk_fpa_geq : context -> ast -> ast -> ast = "n_mk_fpa_geq"
external mk_fpa_gt : context -> ast -> ast -> ast = "n_mk_fpa_gt"
external mk_fpa_eq : context -> ast -> ast -> ast = "n_mk_fpa_eq"
external mk_fpa_is_normal : context -> ast -> ast = "n_mk_fpa_is_normal"
external mk_fpa_is_subnormal : context -> ast -> ast
  = "n_mk_fpa_is_subnormal"
external mk_fpa_is_zero : context -> ast -> ast = "n_mk_fpa_is_zero"
external mk_fpa_is_infinite : context -> ast -> ast = "n_mk_fpa_is_infinite"
external mk_fpa_is_nan : context -> ast -> ast = "n_mk_fpa_is_nan"
external mk_fpa_is_negative : context -> ast -> ast = "n_mk_fpa_is_negative"
external mk_fpa_is_positive : context -> ast -> ast = "n_mk_fpa_is_positive"
external mk_fpa_to_fp_bv : context -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_bv"
external mk_fpa_to_fp_float : context -> ast -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_float"
external mk_fpa_to_fp_real : context -> ast -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_real"
external mk_fpa_to_fp_signed : context -> ast -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_signed"
external mk_fpa_to_fp_unsigned : context -> ast -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_unsigned"
external mk_fpa_to_ubv : context -> ast -> ast -> int -> ast
  = "n_mk_fpa_to_ubv"
external mk_fpa_to_sbv : context -> ast -> ast -> int -> ast
  = "n_mk_fpa_to_sbv"
external mk_fpa_to_real : context -> ast -> ast = "n_mk_fpa_to_real"
external fpa_get_ebits : context -> sort -> int = "n_fpa_get_ebits"
external fpa_get_sbits : context -> sort -> int = "n_fpa_get_sbits"
external fpa_is_numeral_nan : context -> ast -> bool = "n_fpa_is_numeral_nan"
external fpa_is_numeral_inf : context -> ast -> bool = "n_fpa_is_numeral_inf"
external fpa_is_numeral_zero : context -> ast -> bool
  = "n_fpa_is_numeral_zero"
external fpa_is_numeral_normal : context -> ast -> bool
  = "n_fpa_is_numeral_normal"
external fpa_is_numeral_subnormal : context -> ast -> bool
  = "n_fpa_is_numeral_subnormal"
external fpa_is_numeral_positive : context -> ast -> bool
  = "n_fpa_is_numeral_positive"
external fpa_is_numeral_negative : context -> ast -> bool
  = "n_fpa_is_numeral_negative"
external fpa_get_numeral_sign_bv : context -> ast -> ast
  = "n_fpa_get_numeral_sign_bv"
external fpa_get_numeral_significand_bv : context -> ast -> ast
  = "n_fpa_get_numeral_significand_bv"
external fpa_get_numeral_sign : context -> ast -> bool * int
  = "n_fpa_get_numeral_sign"
external fpa_get_numeral_significand_string : context -> ast -> string
  = "n_fpa_get_numeral_significand_string"
external fpa_get_numeral_significand_uint64 : context -> ast -> bool * int
  = "n_fpa_get_numeral_significand_uint64"
external fpa_get_numeral_exponent_string : context -> ast -> bool -> string
  = "n_fpa_get_numeral_exponent_string"
external fpa_get_numeral_exponent_int64 :
  context -> ast -> bool -> bool * int = "n_fpa_get_numeral_exponent_int64"
external fpa_get_numeral_exponent_bv : context -> ast -> bool -> ast
  = "n_fpa_get_numeral_exponent_bv"
external mk_fpa_to_ieee_bv : context -> ast -> ast = "n_mk_fpa_to_ieee_bv"
external mk_fpa_to_fp_int_real : context -> ast -> ast -> ast -> sort -> ast
  = "n_mk_fpa_to_fp_int_real"
external context_of_symbol : symbol -> context = "n_context_of_symbol"
external is_null_symbol : symbol -> bool = "n_is_null_symbol"
external mk_null_symbol : context -> symbol = "n_mk_null_symbol"
external context_of_ast : ast -> context = "n_context_of_ast"
external is_null_ast : ast -> bool = "n_is_null_ast"
external mk_null_ast : context -> ast = "n_mk_null_ast"
external context_of_model : model -> context = "n_context_of_model"
external is_null_model : model -> bool = "n_is_null_model"
external mk_null_model : context -> model = "n_mk_null_model"
external context_of_constructor : constructor -> context
  = "n_context_of_constructor"
external is_null_constructor : constructor -> bool = "n_is_null_constructor"
external mk_null_constructor : context -> constructor
  = "n_mk_null_constructor"
external context_of_constructor_list : constructor_list -> context
  = "n_context_of_constructor_list"
external is_null_constructor_list : constructor_list -> bool
  = "n_is_null_constructor_list"
external mk_null_constructor_list : context -> constructor_list
  = "n_mk_null_constructor_list"
external context_of_solver : solver -> context = "n_context_of_solver"
external is_null_solver : solver -> bool = "n_is_null_solver"
external mk_null_solver : context -> solver = "n_mk_null_solver"
external context_of_goal : goal -> context = "n_context_of_goal"
external is_null_goal : goal -> bool = "n_is_null_goal"
external mk_null_goal : context -> goal = "n_mk_null_goal"
external context_of_tactic : tactic -> context = "n_context_of_tactic"
external is_null_tactic : tactic -> bool = "n_is_null_tactic"
external mk_null_tactic : context -> tactic = "n_mk_null_tactic"
external context_of_params : params -> context = "n_context_of_params"
external is_null_params : params -> bool = "n_is_null_params"
external mk_null_params : context -> params = "n_mk_null_params"
external context_of_probe : probe -> context = "n_context_of_probe"
external is_null_probe : probe -> bool = "n_is_null_probe"
external mk_null_probe : context -> probe = "n_mk_null_probe"
external context_of_stats : stats -> context = "n_context_of_stats"
external is_null_stats : stats -> bool = "n_is_null_stats"
external mk_null_stats : context -> stats = "n_mk_null_stats"
external context_of_ast_vector : ast_vector -> context
  = "n_context_of_ast_vector"
external is_null_ast_vector : ast_vector -> bool = "n_is_null_ast_vector"
external mk_null_ast_vector : context -> ast_vector = "n_mk_null_ast_vector"
external context_of_ast_map : ast_map -> context = "n_context_of_ast_map"
external is_null_ast_map : ast_map -> bool = "n_is_null_ast_map"
external mk_null_ast_map : context -> ast_map = "n_mk_null_ast_map"
external context_of_apply_result : apply_result -> context
  = "n_context_of_apply_result"
external is_null_apply_result : apply_result -> bool
  = "n_is_null_apply_result"
external mk_null_apply_result : context -> apply_result
  = "n_mk_null_apply_result"
external context_of_func_interp : func_interp -> context
  = "n_context_of_func_interp"
external is_null_func_interp : func_interp -> bool = "n_is_null_func_interp"
external mk_null_func_interp : context -> func_interp
  = "n_mk_null_func_interp"
external context_of_func_entry : func_entry -> context
  = "n_context_of_func_entry"
external is_null_func_entry : func_entry -> bool = "n_is_null_func_entry"
external mk_null_func_entry : context -> func_entry = "n_mk_null_func_entry"
external context_of_fixedpoint : fixedpoint -> context
  = "n_context_of_fixedpoint"
external is_null_fixedpoint : fixedpoint -> bool = "n_is_null_fixedpoint"
external mk_null_fixedpoint : context -> fixedpoint = "n_mk_null_fixedpoint"
external context_of_optimize : optimize -> context = "n_context_of_optimize"
external is_null_optimize : optimize -> bool = "n_is_null_optimize"
external mk_null_optimize : context -> optimize = "n_mk_null_optimize"
external context_of_param_descrs : param_descrs -> context
  = "n_context_of_param_descrs"
external is_null_param_descrs : param_descrs -> bool
  = "n_is_null_param_descrs"
external mk_null_param_descrs : context -> param_descrs
  = "n_mk_null_param_descrs"
external context_of_rcf_num : rcf_num -> context = "n_context_of_rcf_num"
external is_null_rcf_num : rcf_num -> bool = "n_is_null_rcf_num"
external mk_null_rcf_num : context -> rcf_num = "n_mk_null_rcf_num"
