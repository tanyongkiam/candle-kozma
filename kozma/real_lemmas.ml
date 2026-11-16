(* ========================================================================= *)
(* General results of real analysis used by the inequality files: bounds on  *)
(* exp and log, derivative-sign arguments, one-sided Taylor bounds for all   *)
(* orders, sinh and cosh in the form (exp x +- inv(exp x)) / 2, rational     *)
(* enclosures of exp, convex and concave functions, sums against integrals,  *)
(* and series.                                                               *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* Elementary bounds on exp and log near the tangent line 1 + x.             *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_GT_1PLUS = prove
 (`!x. ~(x = &0) ==> &1 + x < exp x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&1 + x / &2 < &0` THENL
   [MP_TAC(SPEC `x:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp x = exp(x / &2) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `(&1 + x / &2) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(&1 + x / &2) pow 2 = &1 + x + (x / &2) * (x / &2)`] THEN
    MP_TAC(SPEC `x / &2` REAL_LT_SQUARE) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN
    MP_TAC(SPEC `x / &2` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC]);;

let LOG_LT_STRONG = prove
 (`!x. -- &1 < x /\ ~(x = &0) ==> log(&1 + x) < x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LT_IMP THEN
  ASM_SIMP_TAC[REAL_EXP_GT_1PLUS] THEN ASM_REAL_ARITH_TAC);;

let LOG_GE_DIV = prove
 (`!x. -- &1 < x ==> x / (&1 + x) <= log(&1 + x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + --x / (&1 + x) = inv(&1 + x)` ASSUME_TAC THENL
   [UNDISCH_TAC `-- &1 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `--x / (&1 + x)` LOG_LE_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_INV; REAL_ARITH `-- &1 < x ==> &0 < &1 + x`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC);;

let LOG_GT_DIV = prove
 (`!x. -- &1 < x /\ ~(x = &0) ==> x / (&1 + x) < log(&1 + x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 + --x / (&1 + x) = inv(&1 + x)` ASSUME_TAC THENL
   [UNDISCH_TAC `-- &1 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `--x / (&1 + x)` LOG_LT_STRONG) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `-- &1 < y <=> &0 < &1 + y`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_ENTIRE; REAL_NEG_EQ_0; REAL_INV_EQ_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_INV; REAL_ARITH `-- &1 < x ==> &0 < &1 + x`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC);;

let LOG_GE_DIV_HALF = prove
 (`!x. &0 <= x ==> &2 * x / (&2 + x) <= log(&1 + x)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. log(&1 + x) - &2 * x / (&2 + x)`;
                 `\y. y pow 2 / ((&1 + y) * (&2 + y) pow 2)`;
                 `{x:real | &0 <= x}`; `&0`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
  DISCH_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= y` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* L(t) = ln((1+t)/(1-t)) for 0 <= t < 1:                                    *)
(* 2t + 2t^3/3 <= L(t) <= 2t + 2t^3/(3(1-t^2)); hence 56/81 <= ln 2 <=      *)
(* 25/36 (at t = 1/3), and e lies in [2,3].                                  *)
(* ------------------------------------------------------------------------- *)

let LOG_RATIO_ODD_BOUNDS = prove
 (`!t. &0 <= t /\ t < &1
       ==> &2 * t + &2 * t pow 3 / &3 <= log((&1 + t) / (&1 - t)) /\
           log((&1 + t) / (&1 - t))
             <= &2 * t + &2 * t pow 3 / (&3 * (&1 - t pow 2))`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 <= t ==> &0 < &1 + t`; REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\t. (log(&1 + t) - log(&1 - t)) - (&2 * t + &2 * t pow 3 / &3)`;
      `\t. &2 * t pow 4 / ((&1 + t) * (&1 - t))`;
      `{x:real | &0 <= x /\ x < &1}`; `&0`; `t:real`]
     HAS_REAL_DERIVATIVE_INCREASING_IMP);
    MP_TAC(ISPECL
     [`\t. (&2 * t + &2 * t pow 3 / (&3 * (&1 - t pow 2))) -
           (log(&1 + t) - log(&1 - t))`;
      `\t. &4 / &3 * t pow 4 / ((&1 - t pow 2) pow 2)`;
      `{x:real | &0 <= x /\ x < &1}`; `&0`; `t:real`]
     HAS_REAL_DERIVATIVE_INCREASING_IMP)] THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO; LOG_1; REAL_LT_01] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
  STRIP_TAC THEN BETA_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= y` THEN UNDISCH_TAC `y < &1` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    SUBGOAL_THEN `&0 < &1 - y pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < &1 - y pow 2` THEN
    UNDISCH_TAC `&0 <= y` THEN UNDISCH_TAC `y < &1` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2]]);;

let LOG_2_RATIONAL_BOUNDS = prove
 (`&56 / &81 <= log(&2) /\ log(&2) <= &25 / &36`,
  MP_TAC(SPEC `&1 / &3` LOG_RATIO_ODD_BOUNDS) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]);;

let LOG_2_POS = prove
 (`&0 < log(&2)`,
  MP_TAC LOG_2_RATIONAL_BOUNDS THEN REAL_ARITH_TAC);;

let EXP_1_BOUNDS = prove
 (`&2 <= exp(&1) /\ exp(&1) <= &3`,
  MP_TAC E_APPROX_32 THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity from the sign of the derivative on any real interval: the    *)
(* decreasing form, comparison of two functions, the first-derivative test   *)
(* for a minimum, and functions whose derivative changes sign at most once.  *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_DECREASING_IMP = prove
 (`!f f' s a b.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f' x) (atreal x within s)) /\
        (!x. x IN s ==> f' x <= &0) /\ a IN s /\ b IN s /\ a <= b
        ==> f b <= f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --(f:real->real) x`; `\x. --(f':real->real) x`;
                 `s:real->bool`; `a:real`; `b:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG;
               REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
  REAL_ARITH_TAC);;

let HAS_REAL_DERIVATIVE_LE_IMP_LE = prove
 (`!f g f' g' s a x.
        is_realinterval s /\
        (!y. y IN s ==> (f has_real_derivative f' y) (atreal y within s)) /\
        (!y. y IN s ==> (g has_real_derivative g' y) (atreal y within s)) /\
        (!y. y IN s ==> g' y <= f' y) /\
        a IN s /\ x IN s /\ a <= x /\ g a <= f a
        ==> g x <= f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real->real) x - g x`; `\x. (f':real->real) x - g' x`;
                 `s:real->bool`; `a:real`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SUB; REAL_SUB_LE] THEN ASM_REAL_ARITH_TAC);;

let REAL_DERIVATIVE_SIGN_MINIMUM = prove
 (`!f f' s c x.
        is_realinterval s /\ c IN s /\ x IN s /\
        (!y. y IN s ==> (f has_real_derivative f' y) (atreal y within s)) /\
        (!y. y IN s /\ c <= y ==> &0 <= f' y) /\
        (!y. y IN s /\ y <= c ==> f' y <= &0)
        ==> f c <= f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b:real. a IN s /\ b IN s /\ a <= b
          ==> ?z. z IN s /\ a <= z /\ z <= b /\ f b - f a = f' z * (b - a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
                  REAL_MVT_VERY_SIMPLE) THEN
    SUBGOAL_THEN `real_interval[a,b] SUBSET s` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `s:real->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `real_interval[a,b] SUBSET s` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `(c:real) <= x \/ x <= c`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `x:real`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= fx - fc ==> fc <= fx`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_SUB_LE];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `c:real`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `fc - fx <= &0 ==> fc <= fx`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= &0 ==> &0 <= --a`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let REAL_DERIVATIVE_SIGN_CHANGE_MIN_LE = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f' x) (atreal x within s)) /\
        (!u v. u IN s /\ v IN s /\ u <= v /\ f' u < &0 ==> f' v <= &0)
        ==> !u x v. u IN s /\ v IN s /\ u <= x /\ x <= v
                    ==> min (f u) (f v) <= f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a IN s /\ b IN s ==> real_interval[a,b] SUBSET s`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b y. a IN s /\ b IN s /\ y IN real_interval[a,b]
            ==> ((f:real->real) has_real_derivative f' y)
                (atreal y within real_interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:real->bool` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!y. y IN s /\ u <= y /\ y <= x ==> &0 <= (f':real->real) y` THENL
   [MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `real_interval[u,x]`;
                   `u:real`; `x:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    ASM_SIMP_TAC[IS_REALINTERVAL_INTERVAL; ENDS_IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_INTERVAL_NE_EMPTY] THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
      MAP_EVERY EXISTS_TAC [`u:real`; `x:real`] THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `real_interval[x,v]`;
                   `x:real`; `v:real`] HAS_REAL_DERIVATIVE_DECREASING_IMP) THEN
    ASM_SIMP_TAC[IS_REALINTERVAL_INTERVAL; ENDS_IN_REAL_INTERVAL;
                 REAL_INTERVAL_NE_EMPTY] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
        MAP_EVERY EXISTS_TAC [`x:real`; `v:real`] THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let REAL_DERIVATIVE_SIGN_CHANGE_LE_MAX = prove
 (`!f f' s.
        is_realinterval s /\
        (!x. x IN s ==> (f has_real_derivative f' x) (atreal x within s)) /\
        (!u v. u IN s /\ v IN s /\ u <= v /\ &0 < f' u ==> &0 <= f' v)
        ==> !u x v. u IN s /\ v IN s /\ u <= x /\ x <= v
                    ==> f x <= max (f u) (f v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --(f:real->real) x`; `\x. --(f':real->real) x`;
                 `s:real->bool`] REAL_DERIVATIVE_SIGN_CHANGE_MIN_LE) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`;
                REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `x:real`; `v:real`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of a finite product, and a function continuous at x0 that  *)
(* is nonnegative off a finite set is nonnegative at x0.                     *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_PRODUCT = prove
 (`!s:A->bool f f' x t.
     FINITE s /\
     (!i. i IN s ==> (f i has_real_derivative f' i x) (atreal x within t))
     ==> ((\x. product s (\i. f i x)) has_real_derivative
          sum s (\i. f' i x * product (s DELETE i) (\j. f j x)))
         (atreal x within t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES] THEN
  SUBGOAL_THEN
   `sum s (\i. (f':A->real->real) i x *
               product ((a INSERT s) DELETE i) (\j. f j x)) =
    f a x * sum s (\i. f' i x * product (s DELETE i) (\j. f j x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a INSERT s) DELETE (i:A) = a INSERT (s DELETE i)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DELETE_INSERT] THEN
  SUBGOAL_THEN `s DELETE (a:A) = s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MP_TAC(ISPECL
   [`(f:A->real->real) a`; `(f':A->real->real) a x`;
    `\x. product s (\i. (f:A->real->real) i x)`;
    `sum s (\i. (f':A->real->real) i x * product (s DELETE i) (\j. f j x))`;
    `x:real`; `t:real->bool`] HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
  ASM_REWRITE_TAC[]);;

let REAL_CONTINUOUS_NONNEG_COFINITE = prove
 (`!f x0 e. f real_continuous atreal x0 /\ FINITE e /\
            (!x. ~(x IN e) ==> &0 <= f x)
            ==> &0 <= f x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real->real) real_continuous atreal x0` THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `--((f:real->real) x0)`) THEN
  ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. ~(x0 + d / (&n + &2) IN e)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC(ISPEC `\n. x0 + d / (&n + &2)` INFINITE_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
      REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `&0 < d ==> (d / (&m + &2) = d / (&n + &2) <=> &m = &n)`;
       REAL_OF_NUM_EQ];
      DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN REWRITE_TAC[num_INFINITE] THEN
      REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `e:real->bool` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d / (&n + &2) /\ d / (&n + &2) < d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ;
                 REAL_ARITH `&0 < &n + &2`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MP_TAC(SPECL [`d:real`; `&n`] REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0 + d / (&n + &2)` o
    check (is_forall o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0 + d / (&n + &2)` o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[REAL_ADD_SUB] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Partial sums of the exponential series: below exp x for x >= 0 at every  *)
(* degree and for every x at odd degree, above exp x for x <= 0 at even      *)
(* degree. REAL_EXP_PARTIAL_SUM_LE is the theorem of that name in HOL        *)
(* Light's Baker/extrap.ml (with the quantifiers in the order x, n), which   *)
(* Candle's library does not contain. Replace this local copy by the        *)
(* library theorem once Candle's library includes it.                       *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_EXP_PARTIAL_SUM = prove
 (`!n x. ((\x. sum(0..SUC n) (\k. x pow k / &(FACT k))) has_real_derivative
          sum(0..n) (\k. x pow k / &(FACT k))) (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT)
                       (ARITH_RULE `0 <= SUC n`)] THEN
  REWRITE_TAC[ADD1; SUM_OFFSET] THEN
  REWRITE_TAC[real_pow; FACT; REAL_DIV_1] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `s = &0 + s`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
  REWRITE_TAC[GSYM ADD1; FACT; SUC_SUB1; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `k:num` FACT_LT) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_FIELD);;

let REAL_EXP_PARTIAL_SUM_0 = prove
 (`!n. sum(0..n) (\k. &0 pow k / &(FACT k)) = &1`,
  GEN_TAC THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT) (SPEC `n:num` LE_0)] THEN
  REWRITE_TAC[real_pow; FACT; REAL_DIV_1;
              REAL_ARITH `&1 + s = &1 <=> s = &0`] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  SIMP_TAC[REAL_POW_ZERO; ARITH_RULE `0 + 1 <= i ==> ~(i = 0)`;
           real_div; REAL_MUL_LZERO]);;

let REAL_EXP_PARTIAL_SUM_LE = prove
 (`!n x. &0 <= x ==> sum(0..n) (\k. x pow k / &(FACT k)) <= exp x`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; real_pow; FACT; REAL_DIV_1] THEN
    MESON_TAC[REAL_EXP_LE_X; REAL_ARITH `&0 <= x /\ &1 + x <= e ==> &1 <= e`];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. exp x - sum(0..SUC n) (\k. x pow k / &(FACT k))`;
                 `\x. exp x - sum(0..n) (\k. x pow k / &(FACT k))`;
                 `{x:real | &0 <= x}`; `&0`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_SUB_LE] THEN ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP; HAS_REAL_DERIVATIVE_EXP_PARTIAL_SUM];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_PARTIAL_SUM_0; REAL_EXP_0] THEN REAL_ARITH_TAC);;

let REAL_EXP_NEG_ALTERNATING = prove
 (`!m x. x <= &0
         ==> &0 <= (-- &1) pow m *
                   (sum(0..m) (\k. x pow k / &(FACT k)) - exp x)`,
  let lemma = prove
   (`!m y. ((\y. sum(0..SUC m) (\k. (--y) pow k / &(FACT k)))
            has_real_derivative
            --sum(0..m) (\k. (--y) pow k / &(FACT k))) (atreal y)`,
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`\y:real. --y`;
                   `\y. sum(0..SUC m) (\k. y pow k / &(FACT k))`]
      (INST [`\y. sum(0..m) (\k. y pow k / &(FACT k))`, `g':real->real`;
             `-- &1`, `f':real`]
         HAS_REAL_DERIVATIVE_CHAIN_UNIV)) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP_PARTIAL_SUM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real` o CONJUNCT2) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `-- &1 * x = --x`]]) in
  SUBGOAL_THEN
   `!m y. &0 <= y
          ==> &0 <= (-- &1) pow m *
                    (sum(0..m) (\k. (--y) pow k / &(FACT k)) - exp(--y))`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`m:num`; `--x:real`] th)) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; SUM_SING_NUMSEG; FACT; REAL_DIV_1; REAL_MUL_LID] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\y. (-- &1) pow SUC m *
         (sum(0..SUC m) (\k. (--y) pow k / &(FACT k)) - exp(--y))`;
    `\y:real. &0`;
    `\y. (-- &1) pow SUC m *
         (--sum(0..m) (\k. (--y) pow k / &(FACT k)) - --exp(--y))`;
    `\y:real. &0`; `{y:real | &0 <= y}`; `&0`; `x:real`]
   HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL;
              HAS_REAL_DERIVATIVE_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[lemma] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
    ASM_REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_EXP_PARTIAL_SUM_0] THEN
    REAL_ARITH_TAC]);;

let REAL_EXP_PARTIAL_SUM_ODD_LE = prove
 (`!n x. sum(0..2 * n + 1) (\k. x pow k / &(FACT k)) <= exp x`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= x \/ &0 <= --x`) THENL
   [ASM_SIMP_TAC[REAL_EXP_PARTIAL_SUM_LE];
    MP_TAC(SPECL [`2 * n + 1`; `x:real`] REAL_EXP_NEG_ALTERNATING) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; EVEN_ADD; EVEN_MULT; ARITH] THEN
    REAL_ARITH_TAC]);;

let REAL_EXP_LE_PARTIAL_SUM_EVEN = prove
 (`!n x. x <= &0 ==> exp x <= sum(0..2 * n) (\k. x pow k / &(FACT k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 * n`; `x:real`] REAL_EXP_NEG_ALTERNATING) THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; EVEN_MULT; ARITH] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One-sided Taylor bounds on sin and cos for every order: for x >= 0 the    *)
(* partial sums alternate around sin x, and for every x around cos x.        *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_SIN_PARTIAL_SUM = prove
 (`!m x. ((\x. sum(0..m) (\k. (-- &1) pow k * x pow (2 * k + 1) /
                              &(FACT(2 * k + 1))))
          has_real_derivative
          sum(0..m) (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k))))
         (atreal x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REAL_DIFF_TAC THEN
  REWRITE_TAC[ADD_SUB; GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `2 * k` FACT_LT) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_COS_PARTIAL_SUM = prove
 (`!m x. ((\x. sum(0..SUC m) (\k. (-- &1) pow k *
                                  x pow (2 * k) / &(FACT(2 * k))))
          has_real_derivative
          --sum(0..m) (\k. (-- &1) pow k * x pow (2 * k + 1) /
                           &(FACT(2 * k + 1))))
         (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT)
                       (ARITH_RULE `0 <= SUC m`)] THEN
  REWRITE_TAC[ADD1; SUM_OFFSET] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `--s = &0 + --s`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN REWRITE_TAC[GSYM SUM_NEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; real_pow; FACT; REAL_MUL_LID; REAL_DIV_1;
                HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * (k + 1) = SUC(2 * k + 1)`; SUC_SUB1; FACT;
              GSYM REAL_OF_NUM_MUL; real_pow; REAL_POW_ADD; REAL_POW_1] THEN
  MP_TAC(SPEC `2 * k + 1` FACT_LT) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

let SIN_COS_TAYLOR_ALTERNATING = prove
 (`!m x. &0 <= x
         ==> &0 <= (-- &1) pow m *
                   (sum(0..m) (\k. (-- &1) pow k * x pow (2 * k + 1) /
                                   &(FACT(2 * k + 1))) - sin x) /\
             &0 <= (-- &1) pow m *
                   (sum(0..m) (\k. (-- &1) pow k *
                                   x pow (2 * k) / &(FACT(2 * k))) - cos x)`,
  let sin0 = prove
   (`!m. sum(0..m) (\k. (-- &1) pow k * &0 pow (2 * k + 1) /
                        &(FACT(2 * k + 1))) = &0`,
    GEN_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    REWRITE_TAC[REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC)
  and cos0 = prove
   (`!m. sum(0..SUC m) (\k. (-- &1) pow k * &0 pow (2 * k) /
                            &(FACT(2 * k))) = &1`,
    GEN_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT) (ARITH_RULE `0 <= SUC m`)]
    THEN
    REWRITE_TAC[MULT_CLAUSES; real_pow; FACT; REAL_DIV_1; REAL_MUL_LID;
                REAL_ARITH `&1 + s = &1 <=> s = &0`] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    SIMP_TAC[REAL_POW_ZERO; MULT_EQ_0; ARITH_EQ;
             ARITH_RULE `0 + 1 <= i ==> ~(i = 0)`] THEN REAL_ARITH_TAC) in
  let stepa = prove
   (`!m x. (!y. &0 <= y
                ==> &0 <= (-- &1) pow m *
                          (sum(0..m) (\k. (-- &1) pow k *
                                          y pow (2 * k) / &(FACT(2 * k))) -
                           cos y)) /\
           &0 <= x
           ==> &0 <= (-- &1) pow m *
                     (sum(0..m) (\k. (-- &1) pow k * x pow (2 * k + 1) /
                                     &(FACT(2 * k + 1))) - sin x)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\y. (-- &1) pow m *
           (sum(0..m) (\k. (-- &1) pow k * y pow (2 * k + 1) /
                           &(FACT(2 * k + 1))) - sin y)`;
      `\y:real. &0`;
      `\y. (-- &1) pow m *
           (sum(0..m) (\k. (-- &1) pow k *
                           y pow (2 * k) / &(FACT(2 * k))) - cos y)`;
      `\y:real. &0`; `{y:real | &0 <= y}`; `&0`; `x:real`]
     HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL;
                HAS_REAL_DERIVATIVE_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[sin0; SIN_0; REAL_SUB_REFL; REAL_MUL_RZERO;
                    REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_SIN_PARTIAL_SUM; HAS_REAL_DERIVATIVE_SIN])
  and stepb = prove
   (`!m x. (!y. &0 <= y
                ==> &0 <= (-- &1) pow m *
                          (sum(0..m) (\k. (-- &1) pow k * y pow (2 * k + 1) /
                                          &(FACT(2 * k + 1))) - sin y)) /\
           &0 <= x
           ==> &0 <= (-- &1) pow SUC m *
                     (sum(0..SUC m) (\k. (-- &1) pow k *
                                         x pow (2 * k) / &(FACT(2 * k))) -
                      cos x)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\y. (-- &1) pow SUC m *
           (sum(0..SUC m) (\k. (-- &1) pow k *
                               y pow (2 * k) / &(FACT(2 * k))) - cos y)`;
      `\y:real. &0`;
      `\y. (-- &1) pow SUC m *
           (--sum(0..m) (\k. (-- &1) pow k * y pow (2 * k + 1) /
                             &(FACT(2 * k + 1))) - --sin y)`;
      `\y:real. &0`; `{y:real | &0 <= y}`; `&0`; `x:real`]
     HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL;
                HAS_REAL_DERIVATIVE_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[cos0; COS_0; REAL_SUB_REFL; REAL_MUL_RZERO;
                    REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_COS_PARTIAL_SUM;
                  HAS_REAL_DERIVATIVE_COS];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
      ASM_REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC]) in
  SUBGOAL_THEN
   `!m. (!x. &0 <= x
             ==> &0 <= (-- &1) pow m *
                       (sum(0..m) (\k. (-- &1) pow k *
                                       x pow (2 * k) / &(FACT(2 * k))) -
                        cos x))`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; SUM_SING_NUMSEG; MULT_CLAUSES; FACT;
                  REAL_DIV_1] THEN
      GEN_TAC THEN MP_TAC(SPEC `x:real` COS_BOUND) THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC stepb THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC stepa THEN ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC stepa THEN
    ASM_SIMP_TAC[]]);;

let SIN_TAYLOR_BOUNDS = prove
 (`!n x. &0 <= x
         ==> sum(0..2 * n + 1)
               (\k. (-- &1) pow k * x pow (2 * k + 1) / &(FACT(2 * k + 1)))
             <= sin x /\
             sin x <=
             sum(0..2 * n)
               (\k. (-- &1) pow k * x pow (2 * k + 1) / &(FACT(2 * k + 1)))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`2 * n + 1`; `x:real`] SIN_COS_TAYLOR_ALTERNATING);
    MP_TAC(SPECL [`2 * n`; `x:real`] SIN_COS_TAYLOR_ALTERNATING)] THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; EVEN_ADD; EVEN_MULT; ARITH] THEN
  REAL_ARITH_TAC);;

let COS_TAYLOR_BOUNDS = prove
 (`!n x. sum(0..2 * n + 1) (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k)))
         <= cos x /\
         cos x <=
         sum(0..2 * n) (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!m. sum(0..m) (\k. (-- &1) pow k * x pow (2 * k) / &(FACT(2 * k))) =
        sum(0..m) (\k. (-- &1) pow k * abs x pow (2 * k) / &(FACT(2 * k)))`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW2_ABS];
    ALL_TAC] THEN
  SUBST1_TAC(GSYM(SPEC `x:real` COS_ABS)) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`2 * n + 1`; `abs x`] SIN_COS_TAYLOR_ALTERNATING);
    MP_TAC(SPECL [`2 * n`; `abs x`] SIN_COS_TAYLOR_ALTERNATING)] THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_POW_NEG; REAL_POW_ONE; EVEN_ADD; EVEN_MULT;
              ARITH] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances at a fixed order: EXPAND_PARTIAL_SUM_RULE expands sum(m..n) f   *)
(* for numerals m, n into its terms and evaluates the factorials.            *)
(* ------------------------------------------------------------------------- *)

let EXPAND_PARTIAL_SUM_RULE =
  CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
            ONCE_DEPTH_CONV EXPAND_SUM_CONV THENC
            DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_FACT_CONV THENC
            ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
            ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV THENC
            REWRITE_CONV[real_pow; REAL_POW_1; REAL_DIV_1; REAL_MUL_LID;
                         REAL_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* sinh x and cosh x, written (exp x - inv(exp x)) / 2 and                   *)
(* (exp x + inv(exp x)) / 2 as in the library (REAL_LE_X_SINH): derivatives, *)
(* parity, cosh^2 - sinh^2 = 1, and Taylor bounds for every order: below     *)
(* by the partial sums (sinh for x >= 0, cosh for every x), and above on     *)
(* [0,b] (sinh) and for |x| <= b (cosh) with the last coefficient replaced   *)
(* by any c >= cosh b.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_SINH = prove
 (`!x. ((\x. (exp x - inv(exp x)) / &2) has_real_derivative
        (exp x + inv(exp x)) / &2) (atreal x)`,
  GEN_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[REAL_EXP_NZ] THEN
  MP_TAC(SPEC `x:real` REAL_EXP_NZ) THEN CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_COSH = prove
 (`!x. ((\x. (exp x + inv(exp x)) / &2) has_real_derivative
        (exp x - inv(exp x)) / &2) (atreal x)`,
  GEN_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[REAL_EXP_NZ] THEN
  MP_TAC(SPEC `x:real` REAL_EXP_NZ) THEN CONV_TAC REAL_FIELD);;

let SINH_NEG = prove
 (`!x. (exp(--x) - inv(exp(--x))) / &2 = --((exp x - inv(exp x)) / &2)`,
  REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let COSH_NEG = prove
 (`!x. (exp(--x) + inv(exp(--x))) / &2 = (exp x + inv(exp x)) / &2`,
  REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let COSH_SQUARE_SUB_SINH_SQUARE = prove
 (`!x. ((exp x + inv(exp x)) / &2) pow 2 - ((exp x - inv(exp x)) / &2) pow 2 =
       &1`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_EXP_NZ) THEN CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_SINH_PARTIAL_SUM = prove
 (`!m x. ((\x. sum(0..m) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))))
          has_real_derivative
          sum(0..m) (\k. x pow (2 * k) / &(FACT(2 * k)))) (atreal x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REAL_DIFF_TAC THEN
  REWRITE_TAC[ADD_SUB; GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `2 * k` FACT_LT) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_FIELD);;

let HAS_REAL_DERIVATIVE_COSH_PARTIAL_SUM = prove
 (`!m x. ((\x. sum(0..SUC m) (\k. x pow (2 * k) / &(FACT(2 * k))))
          has_real_derivative
          sum(0..m) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1)))) (atreal x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT)
                       (ARITH_RULE `0 <= SUC m`)] THEN
  REWRITE_TAC[ADD1; SUM_OFFSET] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `s = &0 + s`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; real_pow; FACT; REAL_DIV_1;
                HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REAL_DIFF_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * (k + 1) = SUC(2 * k + 1)`; SUC_SUB1; FACT;
              GSYM REAL_OF_NUM_MUL; real_pow] THEN
  MP_TAC(SPEC `2 * k + 1` FACT_LT) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;

let SINH_PARTIAL_SUM_0 = prove
 (`!m. sum(0..m) (\k. &0 pow (2 * k + 1) / &(FACT(2 * k + 1))) = &0`,
  GEN_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  REWRITE_TAC[REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC);;

let COSH_PARTIAL_SUM_0 = prove
 (`!m. sum(0..m) (\k. &0 pow (2 * k) / &(FACT(2 * k))) = &1`,
  GEN_TAC THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT) (ARITH_RULE `0 <= m`)] THEN
  REWRITE_TAC[MULT_CLAUSES; real_pow; FACT; REAL_DIV_1;
              REAL_ARITH `&1 + s = &1 <=> s = &0`] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  SIMP_TAC[REAL_POW_ZERO; MULT_EQ_0; ARITH_EQ;
           ARITH_RULE `0 + 1 <= i ==> ~(i = 0)`] THEN
  REAL_ARITH_TAC);;

let SINH_COSH_TAYLOR_LOWER = prove
 (`!n x. &0 <= x
         ==> sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) <=
             (exp x - inv(exp x)) / &2 /\
             sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) <=
             (exp x + inv(exp x)) / &2`,
  let cosh_ge_1 = prove
   (`!x. &1 <= (exp x + inv(exp x)) / &2`,
    GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_EXP_POS_LT) THEN
    SPEC_TAC(`exp x`,`e:real`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(e + inv e) / &2 - &1 = (e - &1) pow 2 / (&2 * e)` MP_TAC
    THENL [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MP_TAC(SPECL [`(e - &1) pow 2`; `&2 * e`] REAL_LE_DIV) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC) in
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; MULT_CLAUSES; ADD_CLAUSES; real_pow; FACT;
                REAL_DIV_1; REAL_POW_1; cosh_ge_1; REAL_LE_X_SINH] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_DIV_1; REAL_LE_X_SINH];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!y. &0 <= y ==> sum(0..SUC n) (\k. y pow (2 * k) / &(FACT(2 * k))) <=
                      (exp y + inv(exp y)) / &2`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`\x. (exp x + inv(exp x)) / &2`;
        `\x. sum(0..SUC n) (\k. x pow (2 * k) / &(FACT(2 * k)))`;
        `\x. (exp x - inv(exp x)) / &2`;
        `\x. sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1)))`;
        `{y:real | &0 <= y}`; `&0`; `y:real`]
       HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
      REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; HAS_REAL_DERIVATIVE_COSH;
                   HAS_REAL_DERIVATIVE_COSH_PARTIAL_SUM; REAL_EXP_0;
                   REAL_INV_1] THEN
      REWRITE_TAC[COSH_PARTIAL_SUM_0] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL
       [`\x. (exp x - inv(exp x)) / &2`;
        `\x. sum(0..SUC n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1)))`;
        `\x. (exp x + inv(exp x)) / &2`;
        `\x. sum(0..SUC n) (\k. x pow (2 * k) / &(FACT(2 * k)))`;
        `{y:real | &0 <= y}`; `&0`; `x:real`]
       HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
      REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; HAS_REAL_DERIVATIVE_SINH;
                   HAS_REAL_DERIVATIVE_SINH_PARTIAL_SUM; REAL_EXP_0;
                   REAL_INV_1; SINH_PARTIAL_SUM_0] THEN
      REAL_ARITH_TAC]]);;

let SINH_TAYLOR_LOWER = prove
 (`!n x. &0 <= x
         ==> sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) <=
             (exp x - inv(exp x)) / &2`,
  SIMP_TAC[SINH_COSH_TAYLOR_LOWER]);;

let COSH_TAYLOR_LOWER = prove
 (`!n x. sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) <=
         (exp x + inv(exp x)) / &2`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) =
    sum(0..n) (\k. abs x pow (2 * k) / &(FACT(2 * k))) /\
    (exp x + inv(exp x)) / &2 = (exp(abs x) + inv(exp(abs x))) / &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW2_ABS];
      REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN REWRITE_TAC[COSH_NEG]];
    SIMP_TAC[SINH_COSH_TAYLOR_LOWER; REAL_ABS_POS]]);;

let SINH_COSH_TAYLOR_UPPER = prove
 (`!b c. (exp b + inv(exp b)) / &2 <= c
         ==> !n y. &0 <= y /\ y <= b
                   ==> (exp y + inv(exp y)) / &2 <=
                       sum(0..n) (\k. y pow (2 * k) / &(FACT(2 * k))) +
                       c * y pow (2 * n + 2) / &(FACT(2 * n + 2)) /\
                       (exp y - inv(exp y)) / &2 <=
                       sum(0..n) (\k. y pow (2 * k + 1) / &(FACT(2 * k + 1))) +
                       c * y pow (2 * n + 3) / &(FACT(2 * n + 3))`,
  let powdiv = prove
   (`!c k x. ((\x. c * x pow (k + 1) / &(FACT(k + 1))) has_real_derivative
              c * x pow k / &(FACT k)) (atreal x)`,
    REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN
    REWRITE_TAC[ADD_SUB; GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPEC `k:num` FACT_LT) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC REAL_FIELD) in
  let step = prove
   (`(!P P' b x.
       (!y. (P has_real_derivative P' y) (atreal y)) /\
       (!y. &0 <= y /\ y <= b ==> (exp y + inv(exp y)) / &2 <= P' y) /\
       P(&0) = &0 /\ &0 <= x /\ x <= b
       ==> (exp x - inv(exp x)) / &2 <= P x) /\
     (!P P' b x.
       (!y. (P has_real_derivative P' y) (atreal y)) /\
       (!y. &0 <= y /\ y <= b ==> (exp y - inv(exp y)) / &2 <= P' y) /\
       P(&0) = &1 /\ &0 <= x /\ x <= b
       ==> (exp x + inv(exp x)) / &2 <= P x)`,
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`P:real->real`; `\x. (exp x - inv(exp x)) / &2`;
                     `P':real->real`; `\x. (exp x + inv(exp x)) / &2`;
                     `real_interval[&0,b]`; `&0`; `x:real`]
                    HAS_REAL_DERIVATIVE_LE_IMP_LE);
      MP_TAC(ISPECL [`P:real->real`; `\x. (exp x + inv(exp x)) / &2`;
                     `P':real->real`; `\x. (exp x - inv(exp x)) / &2`;
                     `real_interval[&0,b]`; `&0`; `x:real`]
                    HAS_REAL_DERIVATIVE_LE_IMP_LE)] THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; HAS_REAL_DERIVATIVE_SINH;
                 HAS_REAL_DERIVATIVE_COSH; REAL_EXP_0; REAL_INV_1] THEN
    ASM_REAL_ARITH_TAC) in
  let cosh_le = prove
   (`!b c x. (exp b + inv(exp b)) / &2 <= c /\ &0 <= x /\ x <= b
             ==> (exp x + inv(exp x)) / &2 <= c`,
    REPEAT STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `(exp b + inv(exp b)) / &2` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. (exp x + inv(exp x)) / &2`;
                   `\x. (exp x - inv(exp x)) / &2`;
                   `{y:real | &0 <= y}`; `x:real`; `b:real`]
                  HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN;
                 HAS_REAL_DERIVATIVE_COSH] THEN
    REPEAT STRIP_TAC THENL
     [MP_TAC(SPEC `x':real` REAL_LE_X_SINH) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]) in
  let derivs = prove
   (`!c n x.
       ((\x. sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) +
             c * x pow (2 * n + 3) / &(FACT(2 * n + 3))) has_real_derivative
        sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) +
        c * x pow (2 * n + 2) / &(FACT(2 * n + 2))) (atreal x) /\
       ((\x. sum(0..SUC n) (\k. x pow (2 * k) / &(FACT(2 * k))) +
             c * x pow (2 * SUC n + 2) / &(FACT(2 * SUC n + 2)))
        has_real_derivative
        sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) +
        c * x pow (2 * n + 3) / &(FACT(2 * n + 3))) (atreal x) /\
       ((\x. sum(0..0) (\k. x pow (2 * k) / &(FACT(2 * k))) +
             c * x pow (2 * 0 + 2) / &(FACT(2 * 0 + 2))) has_real_derivative
        c * x) (atreal x)`,
    REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_SINH_PARTIAL_SUM] THEN
      MP_TAC(SPECL [`c:real`; `2 * n + 2`; `x:real`] powdiv) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n + 2) + 1 = 2 * n + 3`];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_COSH_PARTIAL_SUM] THEN
      MP_TAC(SPECL [`c:real`; `2 * n + 3`; `x:real`] powdiv) THEN
      REWRITE_TAC[ARITH_RULE `(2 * n + 3) + 1 = 2 * SUC n + 2`];
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
       [REAL_ARITH `c * x = &0 + c * x`] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[SUM_SING_NUMSEG; MULT_CLAUSES; real_pow; FACT; REAL_DIV_1;
                    HAS_REAL_DERIVATIVE_CONST];
        MP_TAC(SPECL [`c:real`; `1`; `x:real`] powdiv) THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        REWRITE_TAC[num_CONV `1`; FACT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1; REAL_DIV_1]]])
  in
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (!y. &0 <= y /\ y <= b
             ==> (exp y + inv(exp y)) / &2 <=
                 sum(0..n) (\k. y pow (2 * k) / &(FACT(2 * k))) +
                 c * y pow (2 * n + 2) / &(FACT(2 * n + 2)))
        ==> (!y. &0 <= y /\ y <= b
                 ==> (exp y - inv(exp y)) / &2 <=
                     sum(0..n) (\k. y pow (2 * k + 1) / &(FACT(2 * k + 1))) +
                     c * y pow (2 * n + 3) / &(FACT(2 * n + 3)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\x. sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) +
           (c:real) * x pow (2 * n + 3) / &(FACT(2 * n + 3))`;
      `\x. sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) +
           (c:real) * x pow (2 * n + 2) / &(FACT(2 * n + 2))`;
      `b:real`; `y:real`] (CONJUNCT1 step)) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[derivs; SINH_PARTIAL_SUM_0; REAL_POW_ZERO;
                 ARITH_RULE `~(2 * n + 3 = 0)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y. &0 <= y /\ y <= b
          ==> (exp y + inv(exp y)) / &2 <=
              sum(0..n) (\k. y pow (2 * k) / &(FACT(2 * k))) +
              c * y pow (2 * n + 2) / &(FACT(2 * n + 2))`
  ASSUME_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL
     [`\x. sum(0..0) (\k. x pow (2 * k) / &(FACT(2 * k))) +
           (c:real) * x pow (2 * 0 + 2) / &(FACT(2 * 0 + 2))`;
      `\x. (c:real) * x`; `b:real`; `y:real`] (CONJUNCT2 step)) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[derivs; COSH_PARTIAL_SUM_0; REAL_POW_ZERO; ARITH_EQ;
                    ADD_EQ_0; MULT_CLAUSES] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    X_GEN_TAC `z:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. (c:real) * x`; `\x:real. (c:real)`; `b:real`;
                   `z:real`] (CONJUNCT1 step)) THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[cosh_le]];
    MP_TAC(ISPECL
     [`\x. sum(0..SUC n) (\k. x pow (2 * k) / &(FACT(2 * k))) +
           (c:real) * x pow (2 * SUC n + 2) / &(FACT(2 * SUC n + 2))`;
      `\x. sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) +
           (c:real) * x pow (2 * n + 3) / &(FACT(2 * n + 3))`;
      `b:real`; `y:real`] (CONJUNCT2 step)) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[derivs; COSH_PARTIAL_SUM_0; REAL_POW_ZERO;
                 ARITH_RULE `~(2 * SUC n + 2 = 0)`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]]);;

let SINH_TAYLOR_UPPER = prove
 (`!n b c x. (exp b + inv(exp b)) / &2 <= c /\ &0 <= x /\ x <= b
             ==> (exp x - inv(exp x)) / &2 <=
                 sum(0..n) (\k. x pow (2 * k + 1) / &(FACT(2 * k + 1))) +
                 c * x pow (2 * n + 3) / &(FACT(2 * n + 3))`,
  MESON_TAC[SINH_COSH_TAYLOR_UPPER]);;

let COSH_TAYLOR_UPPER = prove
 (`!n b c x. (exp b + inv(exp b)) / &2 <= c /\ abs x <= b
             ==> (exp x + inv(exp x)) / &2 <=
                 sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) +
                 c * x pow (2 * n + 2) / &(FACT(2 * n + 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..n) (\k. x pow (2 * k) / &(FACT(2 * k))) =
    sum(0..n) (\k. abs x pow (2 * k) / &(FACT(2 * k))) /\
    x pow (2 * n + 2) = abs x pow (2 * n + 2) /\
    (exp x + inv(exp x)) / &2 = (exp(abs x) + inv(exp(abs x))) / &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW2_ABS];
      REWRITE_TAC[ARITH_RULE `2 * n + 2 = 2 * (n + 1)`; GSYM REAL_POW_POW;
                  REAL_POW2_ABS];
      REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN REWRITE_TAC[COSH_NEG]];
    MP_TAC(SPECL [`b:real`; `c:real`] SINH_COSH_TAYLOR_UPPER) THEN
    ASM_SIMP_TAC[REAL_ABS_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Rational enclosures of exp: e^x <= ((2n + x)/(2n - x))^n for              *)
(* 0 <= x < 2n, from e^y <= (2 + y)/(2 - y) for 0 <= y < 2, and              *)
(* (sum_(k<=m) (x/n)^k/k!)^n <= e^x for x >= 0.                              *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_LE_RATIO = prove
 (`!x. &0 <= x /\ x < &2 ==> exp x <= (&2 + x) / (&2 - x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&2 * x / (&2 - x)` LOG_GE_DIV_HALF) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&2 * x / (&2 - x)) / (&2 + &2 * x / (&2 - x)) = x /\
    &1 + &2 * x / (&2 - x) = (&2 + x) / (&2 - x)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN UNDISCH_TAC `x < &2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC REAL_LE_TRANS `exp(log((&2 + x) / (&2 - x)))` THEN
  ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC EXP_LOG THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC);;

let REAL_EXP_LE_RATIO_POW = prove
 (`!n x. &0 <= x /\ x < &2 * &n
         ==> exp x <= ((&2 * &n + x) / (&2 * &n - x)) pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x = &n * x / &n /\
                (&2 * &n + x) / (&2 * &n - x) = (&2 + x / &n) / (&2 - x / &n)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT1 th] THEN
             REWRITE_TAC[CONJUNCT2 th]) THENL
   [UNDISCH_TAC `&0 < &n` THEN UNDISCH_TAC `x < &2 * &n` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC REAL_EXP_LE_RATIO THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_EXP_GE_PARTIAL_SUM_POW = prove
 (`!m n x. &0 <= x
           ==> sum(0..m) (\k. (x / &n) pow k / &(FACT k)) pow n <= exp x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_pow] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `exp x = exp(x / &n) pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_EXP_PARTIAL_SUM_LE; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The weighted AM-GM inequality for two terms: x^u y^v <= u x + v y for x,  *)
(* y, u, v >= 0 with u + v = 1. This is AGM_2 of                             *)
(* Multivariate/realanalysis.ml, whose name Library/agm.ml binds to a        *)
(* different theorem. Replace this local copy by the library theorem once    *)
(* the two library theorems no longer share the name AGM_2.                  *)
(* ------------------------------------------------------------------------- *)

let RPOW_MUL_RPOW_LE_WEIGHTED_SUM = prove
 (`!x y u v. &0 <= x /\ &0 <= y /\ &0 <= u /\ &0 <= v /\ u + v = &1
           ==> x rpow u * y rpow v <= u * x + v * y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`\i:num. if i = 0 then u else (v:real)`;
                `\i:num. if i = 0 then x else (y:real)`; `{0,1}`] AGM_GEN) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_MUL_RID]);;

let PRODUCT_RPOW_EQ_EXP_SUM = prove
 (`!s (a:A->real) b.
        FINITE s /\ (!i. i IN s ==> &0 < a i \/ b i = &0)
        ==> product s (\i. a i rpow b i) = exp(sum s (\i. b i * log(a i)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_EXP_SUM] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(i:A) IN s`)) THENL
   [ASM_SIMP_TAC[rpow];
    ASM_REWRITE_TAC[RPOW_0; REAL_MUL_LZERO; REAL_EXP_0]]);;

(* ------------------------------------------------------------------------- *)
(* Convex and concave functions (concave f means (\x. --f x) real_convex_on  *)
(* s, as in the library): concavity from the second derivative, convex      *)
(* functions are integrable, and the supporting line at an interior point.  *)
(* ------------------------------------------------------------------------- *)

let REAL_CONCAVE_ON_SECOND_DERIVATIVE = prove
 (`!f f' f'' s.
        is_realinterval s /\ ~(?a. s = {a}) /\
        (!x. x IN s ==> (f has_real_derivative f' x) (atreal x within s)) /\
        (!x. x IN s ==> (f' has_real_derivative f'' x) (atreal x within s))
        ==> ((\x. --f x) real_convex_on s <=> !x. x IN s ==> f'' x <= &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --(f:real->real) x`; `\x. --(f':real->real) x`;
                 `\x. --(f'':real->real) x`; `s:real->bool`]
                REAL_CONVEX_ON_SECOND_DERIVATIVE) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_NEG] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_NEG_GE0]);;

let REAL_INTEGRABLE_CONVEX = prove
 (`!f a b. f real_convex_on real_interval[a,b]
           ==> f real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[REAL_CONVEX_ON; REAL_INTEGRABLE_ON;
              IMAGE_LIFT_REAL_INTERVAL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_BOUNDED_VARIATION THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC CONVEX_HAS_BOUNDED_VARIATION THEN ASM_REWRITE_TAC[]);;

let REAL_CONVEX_ON_SUPPORTING_LINE = prove
 (`!f s x. f real_convex_on s /\ is_realinterval s /\
           (?a b. a IN s /\ b IN s /\ a < x /\ x < b)
           ==> ?c. !y. y IN s ==> f x + c * (y - x) <= f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. u IN s /\ v IN s /\ u < x /\ x < v
          ==> ((f:real->real) x - f u) / (x - u) <= (f v - f x) / (v - x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `s:real->bool`]
                  REAL_CONVEX_ON_LEFT_SECANT) THEN
    MP_TAC(ISPECL [`f:real->real`; `s:real->bool`]
                  REAL_CONVEX_ON_RIGHT_SECANT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real`; `v:real`; `x:real`]) THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(MP_TAC o SPECL [`u:real`; `v:real`; `x:real`]) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[REAL_SEGMENT_INTERVAL; IN_REAL_INTERVAL] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_SIMP_TAC[REAL_ARITH `u < x ==> abs(x - u) = x - u`;
                 REAL_ARITH `x < v ==> abs(v - x) = v - x`;
                 REAL_ARITH `u < x /\ x < v ==> abs(v - u) = v - u`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `sup {((f:real->real) x - f u) / (x - u) | u | u IN s /\ u < x}` THEN
  MP_TAC(ISPEC `{((f:real->real) x - f u) / (x - u) | u | u IN s /\ u < x}`
               SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `((f:real->real) b - f x) / (b - x)` THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ABBREV_TAC
   `c = sup {((f:real->real) x - f u) / (x - u) | u | u IN s /\ u < x}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `(y:real) < x \/ y = x \/ x < y`)
  THENL
   [REMOVE_THEN "ub" (MP_TAC o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`(f:real->real) x - f y`; `c:real`; `x - y:real`]
                 REAL_LE_LDIV_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(REAL_RING `c * (y - x) = --(c * (x - y:real))`) THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `c <= ((f:real->real) y - f x) / (y - x)` MP_TAC THENL
     [REMOVE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      MP_TAC(SPECL [`c:real`; `(f:real->real) y - f x`; `y - x:real`]
                   REAL_LE_RDIV_EQ) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Integrals: for f continuous and strictly increasing on [a,b] with inverse *)
(* g, int_a^b f + int_(f a)^(f b) g = b f(b) - a f(a); and sums against      *)
(* integrals for decreasing f (the increasing forms are in convexity.ml).    *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_ADD_INVERSE_FUNCTION = prove
 (`!f g a b. a <= b /\ f real_continuous_on real_interval[a,b] /\
             (!x y. x IN real_interval[a,b] /\ y IN real_interval[a,b] /\ x < y
                    ==> f x < f y) /\
             (!x. x IN real_interval[a,b] ==> g(f x) = x)
             ==> g real_integrable_on real_interval[f a,f b] /\
                 real_integral (real_interval[a,b]) f +
                 real_integral (real_interval[f a,f b]) g = b * f b - a * f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "strict" o REWRITE_RULE[IN_REAL_INTERVAL])
    (LABEL_TAC "inv" o REWRITE_RULE[IN_REAL_INTERVAL])) THEN
  SUBGOAL_THEN
   `!x y. a <= x /\ x <= b /\ a <= y /\ y <= b /\ x <= y
          ==> (f:real->real) x <= f y`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = y` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "strict" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (f:real->real) a <= s /\ s <= f b
        ==> a <= (g:real->real) s /\ g s <= b /\ f(g s) = s`
  (LABEL_TAC "ginv") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `s:real`]
                  REAL_IVT_INCREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y s. a <= x /\ y <= b /\ x <= y /\ (f:real->real) x <= s /\ s <= f y
            ==> x <= (g:real->real) s /\ g s <= y`
  (LABEL_TAC "rng") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real->real) a <= f x /\ f y <= f b`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ginv" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "strict" (MP_TAC o SPECL [`(g:real->real) s`; `x:real`]);
      USE_THEN "strict" (MP_TAC o SPECL [`y:real`; `(g:real->real) s`])] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. a <= u /\ v <= b
          ==> (f:real->real) real_integrable_on real_interval[u,v]`
  (LABEL_TAC "intf") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. (f:real->real) a <= u /\ v <= f b
          ==> (g:real->real) real_integrable_on real_interval[u,v]`
  (LABEL_TAC "intg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_INCREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "ginv" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "rng"
     (MP_TAC o SPECL [`(g:real->real) s`; `b:real`; `t:real`]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "intg" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. a <= x /\ x <= y /\ y <= b
          ==> abs((real_integral (real_interval[a,y]) f +
                   real_integral (real_interval[(f:real->real) a,f y]) g -
                   y * f y) -
                  (real_integral (real_interval[a,x]) f +
                   real_integral (real_interval[f a,f x]) g - x * f x))
              <= (y - x) * (f y - f x)`
  (LABEL_TAC "core") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:real->real) a <= f x /\ f x <= f y /\ f y <= f b`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `y:real`; `x:real`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "intf" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`g:real->real`; `(f:real->real) a`; `(f:real->real) y`;
                   `(f:real->real) x`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "intg" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(INST [`(f:real->real) x`,`B:real`]
           (ISPECL [`f:real->real`; `x:real`; `y:real`]
                   REAL_INTEGRAL_LBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    MP_TAC(INST [`(f:real->real) y`,`B:real`]
           (ISPECL [`f:real->real`; `x:real`; `y:real`]
                   REAL_INTEGRAL_UBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    MP_TAC(INST [`x:real`,`B:real`]
           (ISPECL [`g:real->real`; `(f:real->real) x`; `(f:real->real) y`]
                   REAL_INTEGRAL_LBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intg" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        USE_THEN "rng" (MP_TAC o SPECL [`x:real`; `y:real`; `x':real`]) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    MP_TAC(INST [`y:real`,`B:real`]
           (ISPECL [`g:real->real`; `(f:real->real) x`; `(f:real->real) y`]
                   REAL_INTEGRAL_UBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intg" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        USE_THEN "rng" (MP_TAC o SPECL [`x:real`; `y:real`; `x':real`]) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. real_integral (real_interval[a,x]) f +
         real_integral (real_interval[(f:real->real) a,f x]) g - x * f x`;
    `real_interval[a,b]`; `--(a * (f:real->real) a)`; `a:real`]
   HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_LE_REFL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\y. abs((f:real->real) y - f x)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_REAL_INTERVAL] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    DISJ_CASES_TAC(SPECL [`x:real`; `y:real`] REAL_LE_TOTAL) THENL
     [USE_THEN "core" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "mono" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN
       `abs((f:real->real) y - f x) = f y - f x /\ abs(y - x) = y - x`
      (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "core" (MP_TAC o SPECL [`y:real`; `x:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "mono" (MP_TAC o SPECL [`y:real`; `x:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN
       `abs((f:real->real) y - f x) = f x - f y /\ abs(y - x) = x - y`
      (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REALLIM_NULL_ABS] THEN REWRITE_TAC[GSYM REALLIM_NULL] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_WITHINREAL] THEN
    USE_THEN "cont"
     (MP_TAC o REWRITE_RULE[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL]]);;

let SUM_LE_REAL_INTEGRAL_DECREASING = prove
 (`!f a n. (!x y. a <= x /\ x <= y /\ y <= a + &n ==> f y <= f x)
           ==> sum(1..n) (\k. f(a + &k)) <=
               real_integral (real_interval[a,a + &n]) f`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_RID; REAL_INTEGRAL_REFL;
                REAL_LE_REFL];
    DISCH_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN
  SUBGOAL_THEN `(f:real->real) real_integrable_on real_interval[a,a + &n + &1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `a + &n + &1`; `a + &n`]
                REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(INST [`(f:real->real)(a + &n + &1)`,`B:real`]
           (ISPECL [`f:real->real`; `a + &n`; `a + &n + &1`]
                   REAL_INTEGRAL_LBOUND)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`a:real`; `a + &n + &1`] THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let REAL_INTEGRAL_LE_SUM_DECREASING = prove
 (`!f a n. (!x y. a + &1 <= x /\ x <= y /\ y <= a + &n + &1 ==> f y <= f x)
           ==> real_integral (real_interval[a + &1,a + &n + &1]) f <=
               sum(1..n) (\k. f(a + &k))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_LID; REAL_INTEGRAL_REFL;
                REAL_LE_REFL];
    DISCH_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN
  SUBGOAL_THEN
   `(f:real->real) real_integrable_on real_interval[a + &1,a + (&n + &1) + &1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `a + &1`; `a + (&n + &1) + &1`;
                 `a + &n + &1`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(INST [`(f:real->real)(a + &n + &1)`,`B:real`]
           (ISPECL [`f:real->real`; `a + &n + &1`; `a + (&n + &1) + &1`]
                   REAL_INTEGRAL_UBOUND)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`a + &1`; `a + (&n + &1) + &1`] THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Series: a nonnegative series with bounded partial sums converges, with    *)
(* sum at most the bound; the product of two square-summable sequences is    *)
(* absolutely summable; and atn t >= t / (1 + t^2) for t >= 0.               *)
(* REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS is REAL_SUMMABLE_POS_PARTIAL_BOUND *)
(* of HOL Light's Multivariate/realanalysis.ml, which Candle's copy of that  *)
(* file does not yet contain. Replace this local copy by the library theorem *)
(* once Candle's library includes it.                                        *)
(* ------------------------------------------------------------------------- *)

let REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS = prove
 (`!f:num->real k B.
        (!n. k <= n ==> &0 <= f n) /\ (!n. sum(k..n) f <= B)
        ==> real_summable (from k) f /\ real_infsum (from k) f <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. &0 <= sum(k..n) (f:num->real)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. sum(k..n) (f:num->real)`
    CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `abs B + &1:real` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
          free_in `B:real` (concl th))) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC];
      DISJ1_TAC THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_ADDR; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
  SUBGOAL_THEN `((f:num->real) real_sums l) (from k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SERIES_FROM]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_summable]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INFSUM_UNIQUE) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n. sum(k..n) (f:num->real)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  MESON_TAC[]);;

let REAL_SUMMABLE_ABS_MUL_SQUARES = prove
 (`!s (a:num->real) b.
        real_summable s (\n. a n pow 2) /\ real_summable s (\n. b n pow 2)
        ==> real_summable s (\n. abs(a n * b n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n. inv(&2) * (a n pow 2 + (b:num->real) n pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN MATCH_MP_TAC REAL_SUMMABLE_ADD THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_ABS; REAL_ABS_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    SPEC_TAC(`abs((a:num->real) n)`, `x:real`) THEN
    SPEC_TAC(`abs((b:num->real) n)`, `y:real`) THEN REPEAT GEN_TAC THEN
    MP_TAC(SPEC `x - y:real` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let ATN_GE_DIV = prove
 (`!t. &0 <= t ==> t / (&1 + t pow 2) <= atn t`,
  GEN_TAC THEN ASM_CASES_TAC `t = &0` THEN
  ASM_REWRITE_TAC[ATN_0; real_div; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  DISCH_TAC THEN SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`atn`; `\x. inv(&1 + x pow 2)`; `&0`; `t:real`] REAL_MVT) THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_ATN; HAS_REAL_DERIVATIVE_ATN] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; ATN_0; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `!x y:real. x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;
