type lbool = L_FALSE | L_UNDEF | L_TRUE
val int_of_lbool : lbool -> int
val lbool_of_int : int -> lbool
type symbol_kind = INT_SYMBOL | STRING_SYMBOL
val int_of_symbol_kind : symbol_kind -> int
val symbol_kind_of_int : int -> symbol_kind
type parameter_kind =
    PARAMETER_INT
  | PARAMETER_DOUBLE
  | PARAMETER_RATIONAL
  | PARAMETER_SYMBOL
  | PARAMETER_SORT
  | PARAMETER_AST
  | PARAMETER_FUNC_DECL
val int_of_parameter_kind : parameter_kind -> int
val parameter_kind_of_int : int -> parameter_kind
type sort_kind =
    UNINTERPRETED_SORT
  | BOOL_SORT
  | INT_SORT
  | REAL_SORT
  | BV_SORT
  | ARRAY_SORT
  | DATATYPE_SORT
  | RELATION_SORT
  | FINITE_DOMAIN_SORT
  | FLOATING_POINT_SORT
  | ROUNDING_MODE_SORT
  | SEQ_SORT
  | RE_SORT
  | UNKNOWN_SORT
val int_of_sort_kind : sort_kind -> int
val sort_kind_of_int : int -> sort_kind
type ast_kind =
    NUMERAL_AST
  | APP_AST
  | VAR_AST
  | QUANTIFIER_AST
  | SORT_AST
  | FUNC_DECL_AST
  | UNKNOWN_AST
val int_of_ast_kind : ast_kind -> int
val ast_kind_of_int : int -> ast_kind
type decl_kind =
    OP_TRUE
  | OP_FALSE
  | OP_EQ
  | OP_DISTINCT
  | OP_ITE
  | OP_AND
  | OP_OR
  | OP_IFF
  | OP_XOR
  | OP_NOT
  | OP_IMPLIES
  | OP_OEQ
  | OP_INTERP
  | OP_ANUM
  | OP_AGNUM
  | OP_LE
  | OP_GE
  | OP_LT
  | OP_GT
  | OP_ADD
  | OP_SUB
  | OP_UMINUS
  | OP_MUL
  | OP_DIV
  | OP_IDIV
  | OP_REM
  | OP_MOD
  | OP_TO_REAL
  | OP_TO_INT
  | OP_IS_INT
  | OP_POWER
  | OP_STORE
  | OP_SELECT
  | OP_CONST_ARRAY
  | OP_ARRAY_MAP
  | OP_ARRAY_DEFAULT
  | OP_SET_UNION
  | OP_SET_INTERSECT
  | OP_SET_DIFFERENCE
  | OP_SET_COMPLEMENT
  | OP_SET_SUBSET
  | OP_AS_ARRAY
  | OP_ARRAY_EXT
  | OP_BNUM
  | OP_BIT1
  | OP_BIT0
  | OP_BNEG
  | OP_BADD
  | OP_BSUB
  | OP_BMUL
  | OP_BSDIV
  | OP_BUDIV
  | OP_BSREM
  | OP_BUREM
  | OP_BSMOD
  | OP_BSDIV0
  | OP_BUDIV0
  | OP_BSREM0
  | OP_BUREM0
  | OP_BSMOD0
  | OP_ULEQ
  | OP_SLEQ
  | OP_UGEQ
  | OP_SGEQ
  | OP_ULT
  | OP_SLT
  | OP_UGT
  | OP_SGT
  | OP_BAND
  | OP_BOR
  | OP_BNOT
  | OP_BXOR
  | OP_BNAND
  | OP_BNOR
  | OP_BXNOR
  | OP_CONCAT
  | OP_SIGN_EXT
  | OP_ZERO_EXT
  | OP_EXTRACT
  | OP_REPEAT
  | OP_BREDOR
  | OP_BREDAND
  | OP_BCOMP
  | OP_BSHL
  | OP_BLSHR
  | OP_BASHR
  | OP_ROTATE_LEFT
  | OP_ROTATE_RIGHT
  | OP_EXT_ROTATE_LEFT
  | OP_EXT_ROTATE_RIGHT
  | OP_BIT2BOOL
  | OP_INT2BV
  | OP_BV2INT
  | OP_CARRY
  | OP_XOR3
  | OP_BSMUL_NO_OVFL
  | OP_BUMUL_NO_OVFL
  | OP_BSMUL_NO_UDFL
  | OP_BSDIV_I
  | OP_BUDIV_I
  | OP_BSREM_I
  | OP_BUREM_I
  | OP_BSMOD_I
  | OP_PR_UNDEF
  | OP_PR_TRUE
  | OP_PR_ASSERTED
  | OP_PR_GOAL
  | OP_PR_MODUS_PONENS
  | OP_PR_REFLEXIVITY
  | OP_PR_SYMMETRY
  | OP_PR_TRANSITIVITY
  | OP_PR_TRANSITIVITY_STAR
  | OP_PR_MONOTONICITY
  | OP_PR_QUANT_INTRO
  | OP_PR_DISTRIBUTIVITY
  | OP_PR_AND_ELIM
  | OP_PR_NOT_OR_ELIM
  | OP_PR_REWRITE
  | OP_PR_REWRITE_STAR
  | OP_PR_PULL_QUANT
  | OP_PR_PULL_QUANT_STAR
  | OP_PR_PUSH_QUANT
  | OP_PR_ELIM_UNUSED_VARS
  | OP_PR_DER
  | OP_PR_QUANT_INST
  | OP_PR_HYPOTHESIS
  | OP_PR_LEMMA
  | OP_PR_UNIT_RESOLUTION
  | OP_PR_IFF_TRUE
  | OP_PR_IFF_FALSE
  | OP_PR_COMMUTATIVITY
  | OP_PR_DEF_AXIOM
  | OP_PR_DEF_INTRO
  | OP_PR_APPLY_DEF
  | OP_PR_IFF_OEQ
  | OP_PR_NNF_POS
  | OP_PR_NNF_NEG
  | OP_PR_NNF_STAR
  | OP_PR_CNF_STAR
  | OP_PR_SKOLEMIZE
  | OP_PR_MODUS_PONENS_OEQ
  | OP_PR_TH_LEMMA
  | OP_PR_HYPER_RESOLVE
  | OP_RA_STORE
  | OP_RA_EMPTY
  | OP_RA_IS_EMPTY
  | OP_RA_JOIN
  | OP_RA_UNION
  | OP_RA_WIDEN
  | OP_RA_PROJECT
  | OP_RA_FILTER
  | OP_RA_NEGATION_FILTER
  | OP_RA_RENAME
  | OP_RA_COMPLEMENT
  | OP_RA_SELECT
  | OP_RA_CLONE
  | OP_FD_CONSTANT
  | OP_FD_LT
  | OP_SEQ_UNIT
  | OP_SEQ_EMPTY
  | OP_SEQ_CONCAT
  | OP_SEQ_PREFIX
  | OP_SEQ_SUFFIX
  | OP_SEQ_CONTAINS
  | OP_SEQ_EXTRACT
  | OP_SEQ_REPLACE
  | OP_SEQ_AT
  | OP_SEQ_LENGTH
  | OP_SEQ_INDEX
  | OP_SEQ_TO_RE
  | OP_SEQ_IN_RE
  | OP_STR_TO_INT
  | OP_INT_TO_STR
  | OP_RE_PLUS
  | OP_RE_STAR
  | OP_RE_OPTION
  | OP_RE_CONCAT
  | OP_RE_UNION
  | OP_RE_RANGE
  | OP_RE_LOOP
  | OP_RE_INTERSECT
  | OP_RE_EMPTY_SET
  | OP_RE_FULL_SET
  | OP_RE_COMPLEMENT
  | OP_LABEL
  | OP_LABEL_LIT
  | OP_DT_CONSTRUCTOR
  | OP_DT_RECOGNISER
  | OP_DT_ACCESSOR
  | OP_DT_UPDATE_FIELD
  | OP_PB_AT_MOST
  | OP_PB_AT_LEAST
  | OP_PB_LE
  | OP_PB_GE
  | OP_PB_EQ
  | OP_FPA_RM_NEAREST_TIES_TO_EVEN
  | OP_FPA_RM_NEAREST_TIES_TO_AWAY
  | OP_FPA_RM_TOWARD_POSITIVE
  | OP_FPA_RM_TOWARD_NEGATIVE
  | OP_FPA_RM_TOWARD_ZERO
  | OP_FPA_NUM
  | OP_FPA_PLUS_INF
  | OP_FPA_MINUS_INF
  | OP_FPA_NAN
  | OP_FPA_PLUS_ZERO
  | OP_FPA_MINUS_ZERO
  | OP_FPA_ADD
  | OP_FPA_SUB
  | OP_FPA_NEG
  | OP_FPA_MUL
  | OP_FPA_DIV
  | OP_FPA_REM
  | OP_FPA_ABS
  | OP_FPA_MIN
  | OP_FPA_MAX
  | OP_FPA_FMA
  | OP_FPA_SQRT
  | OP_FPA_ROUND_TO_INTEGRAL
  | OP_FPA_EQ
  | OP_FPA_LT
  | OP_FPA_GT
  | OP_FPA_LE
  | OP_FPA_GE
  | OP_FPA_IS_NAN
  | OP_FPA_IS_INF
  | OP_FPA_IS_ZERO
  | OP_FPA_IS_NORMAL
  | OP_FPA_IS_SUBNORMAL
  | OP_FPA_IS_NEGATIVE
  | OP_FPA_IS_POSITIVE
  | OP_FPA_FP
  | OP_FPA_TO_FP
  | OP_FPA_TO_FP_UNSIGNED
  | OP_FPA_TO_UBV
  | OP_FPA_TO_SBV
  | OP_FPA_TO_REAL
  | OP_FPA_TO_IEEE_BV
  | OP_FPA_MIN_I
  | OP_FPA_MAX_I
  | OP_INTERNAL
  | OP_UNINTERPRETED
val int_of_decl_kind : decl_kind -> int
val decl_kind_of_int : int -> decl_kind
type param_kind =
    PK_UINT
  | PK_BOOL
  | PK_DOUBLE
  | PK_SYMBOL
  | PK_STRING
  | PK_OTHER
  | PK_INVALID
val int_of_param_kind : param_kind -> int
val param_kind_of_int : int -> param_kind
type ast_print_mode =
    PRINT_SMTLIB_FULL
  | PRINT_LOW_LEVEL
  | PRINT_SMTLIB_COMPLIANT
  | PRINT_SMTLIB2_COMPLIANT
val int_of_ast_print_mode : ast_print_mode -> int
val ast_print_mode_of_int : int -> ast_print_mode
type error_code =
    OK
  | SORT_ERROR
  | IOB
  | INVALID_ARG
  | PARSER_ERROR
  | NO_PARSER
  | INVALID_PATTERN
  | MEMOUT_FAIL
  | FILE_ACCESS_ERROR
  | INTERNAL_FATAL
  | INVALID_USAGE
  | DEC_REF_ERROR
  | EXCEPTION
val int_of_error_code : error_code -> int
val error_code_of_int : int -> error_code
type goal_prec = GOAL_PRECISE | GOAL_UNDER | GOAL_OVER | GOAL_UNDER_OVER
val int_of_goal_prec : goal_prec -> int
val goal_prec_of_int : int -> goal_prec
