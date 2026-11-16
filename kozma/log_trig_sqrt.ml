(* ========================================================================= *)
(* Bounds on the logarithm, trigonometric and hyperbolic functions and       *)
(* square roots, from L. Kozma, "Useful Inequalities" (v0.44).               *)
(* ========================================================================= *)

needs "kozma/bernoulli_exp.ml";;

(* ------------------------------------------------------------------------- *)
(* x/(1+x) <= ln(1+x) <= x(6+x)/(6+4x) <= x for x > -1.                      *)
(* ------------------------------------------------------------------------- *)

let LOG_LE_PADE = prove
 (`!x. -- &1 < x ==> log(&1 + x) <= x * (&6 + x) / (&6 + &4 * x)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. x * (&6 + x) / (&6 + &4 * x) - log(&1 + x)`;
                 `\y. &4 * y pow 3 / ((&6 + &4 * y) pow 2 * (&1 + y))`;
                 `{x:real | -- &1 < x}`; `&0`; `x:real`]
                REAL_DERIVATIVE_SIGN_MINIMUM) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 + y /\ &0 < &6 + &4 * y` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LE_POW_2;
                 REAL_ARITH `-- &1 < y ==> &0 <= &1 + y`];
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --b ==> &4 * b <= &0`) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_RING `--((y:real) pow 3) = --y * y pow 2`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2;
                   REAL_ARITH `-- &1 < y ==> &0 <= &1 + y`]]]);;

let LOG_RATIONAL_BOUNDS = prove
 (`!x. -- &1 < x
       ==> x / (&1 + x) <= log(&1 + x) /\
           log(&1 + x) <= x * (&6 + x) / (&6 + &4 * x) /\
           x * (&6 + x) / (&6 + &4 * x) <= x`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[LOG_GE_DIV] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LOG_LE_PADE];
    SUBGOAL_THEN `&0 < &6 + &4 * x` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* ln x <= (x - 1/x)/2 for x >= 1.                                           *)
(* ------------------------------------------------------------------------- *)

let LOG_LE_HALF_DIFF_INV = prove
 (`!x. &1 <= x ==> log x <= (x - inv x) / &2`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. (x - inv x) / &2 - log x`;
                 `\x. (&1 - inv x) pow 2 / &2`;
                 `{x:real | &1 <= x}`; `&1`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_INV_1; LOG_1] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REAL_DIFF_TAC THEN
      UNDISCH_TAC `&1 <= y` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2/(2+x) <= 1/sqrt(1 + x + x^2/12) <= ln(1+x)/x <= 1/sqrt(1+x)             *)
(*   <= (2+x)/(2+2x) for x > -1. The middle links involve ln(1+x)/x and are  *)
(* stated for x <> 0, where it is defined.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_LOG_SQRT_LEMMA = prove
 (`!y. -- &1 < y
       ==> ((\x. log(&1 + x) - x / sqrt(&1 + x + x pow 2 / &12))
            has_real_derivative
            (inv(&1 + y) -
             (&1 + y / &2) /
             ((&1 + y + y pow 2 / &12) * sqrt(&1 + y + y pow 2 / &12))))
           (atreal y)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  SUBGOAL_THEN `&0 < &1 + y + y pow 2 / &12` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ;
               REAL_ARITH `-- &1 < y ==> &0 < &1 + y`] THEN
  MP_TAC(SPEC `&1 + y + y pow 2 / &12` SQRT_POW_2) THEN
  MP_TAC(SPEC `&1 + y + y pow 2 / &12` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 + y + y pow 2 / &12)`,`s:real`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `-- &1 < y` THEN UNDISCH_TAC `&0 < s` THEN
  UNDISCH_TAC `s pow 2 = &1 + y + y pow 2 / &12` THEN CONV_TAC REAL_FIELD);;

let LOG_SQRT_DERIVATIVE_POS = prove
 (`!y. -- &1 < y
       ==> &0 <= inv(&1 + y) -
                 (&1 + y / &2) /
                 ((&1 + y + y pow 2 / &12) * sqrt(&1 + y + y pow 2 / &12))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + y + y pow 2 / &12` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&1 + y + y pow 2 / &12` SQRT_POW_2) THEN
  MP_TAC(SPEC `&1 + y + y pow 2 / &12` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 + y + y pow 2 / &12)`,`s:real`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + y) * (&1 + y / &2) <= (&1 + y + y pow 2 / &12) * s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= y pow 4 * (y pow 2 + &36 * y + &36)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_RING `(y:real) pow 4 = (y pow 2) pow 2`;
                  REAL_LE_POW_2] THEN
      MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    REWRITE_TAC[REAL_SUB_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `-- &1 < y ==> &0 < &1 + y`] THEN
    ASM_REAL_ARITH_TAC]);;

let LOG_SQRT_PADE_SIGN = prove
 (`!x. -- &1 < x
       ==> (&0 <= x ==> x / sqrt(&1 + x + x pow 2 / &12) <= log(&1 + x)) /\
           (x <= &0 ==> log(&1 + x) <= x / sqrt(&1 + x + x pow 2 / &12))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b. -- &1 < a /\ -- &1 < b /\ a <= b
          ==> log(&1 + a) - a / sqrt(&1 + a + a pow 2 / &12) <=
              log(&1 + b) - b / sqrt(&1 + b + b pow 2 / &12)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\x. log(&1 + x) - x / sqrt(&1 + x + x pow 2 / &12)`;
      `\y. inv(&1 + y) -
           (&1 + y / &2) /
           ((&1 + y + y pow 2 / &12) * sqrt(&1 + y + y pow 2 / &12))`;
      `{x:real | -- &1 < x}`; `a:real`; `b:real`]
     HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN BETA_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG_SQRT_LEMMA];
      ASM_SIMP_TAC[LOG_SQRT_DERIVATIVE_POS]];
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`&0`; `x:real`] th) THEN
      MP_TAC(SPECL [`x:real`; `&0`] th)) THEN
    ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1; real_div; REAL_MUL_LZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let LOG_SQRT_BOUNDS = prove
 (`!x. -- &1 < x
       ==> &2 / (&2 + x) <= inv(sqrt(&1 + x + x pow 2 / &12)) /\
           inv(sqrt(&1 + x)) <= (&2 + x) / (&2 + &2 * x) /\
           (~(x = &0)
            ==> inv(sqrt(&1 + x + x pow 2 / &12)) <= log(&1 + x) / x /\
                log(&1 + x) / x <= inv(sqrt(&1 + x)))`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `x:real` LOG_SQRT_PADE_SIGN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x + x pow 2 / &12 /\ &0 < &1 + x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 + x) = &2 * log(sqrt(&1 + x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_POW; SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC
   `x <= &0 ==> log (&1 + x) <= x / sqrt (&1 + x + x pow 2 / &12)` THEN
  UNDISCH_TAC
   `&0 <= x ==> x / sqrt (&1 + x + x pow 2 / &12) <= log (&1 + x)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `sqrt(&1 + x)` LOG_LE_HALF_DIFF_INV) THEN
  MP_TAC(SPEC `inv(sqrt(&1 + x))` LOG_LE_HALF_DIFF_INV) THEN
  ASM_SIMP_TAC[LOG_INV; REAL_INV_INV; SQRT_POS_LT] THEN
  MP_TAC(SPEC `&1 + x + x pow 2 / &12` SQRT_POW_2) THEN
  MP_TAC(SPEC `&1 + x + x pow 2 / &12` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&1 + x` SQRT_POW_2) THEN MP_TAC(SPEC `&1 + x` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt(&1 + x + x pow 2 / &12)`,`s:real`) THEN
  SPEC_TAC(`sqrt(&1 + x)`,`t:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `t - inv t = x * inv t /\
    (&2 + x) / (&2 + &2 * x) = (&1 + t pow 2) / (&2 * t pow 2) /\
    &2 / (&2 + x) = inv((&2 + x) / &2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `&0 < t` THEN
    UNDISCH_TAC `t pow 2 = &1 + x` THEN UNDISCH_TAC `-- &1 < x` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
                 REAL_ARITH `&0 < &1 + x ==> &0 < &2 * (&1 + x)`] THEN
    SUBGOAL_THEN `inv t * &2 * (&1 + x) = &2 * t` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t pow 2 = &1 + x` THEN
      CONV_TAC REAL_FIELD;
      MP_TAC(SPEC `t - &1` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN ASM_CASES_TAC `&0 < x` THENL
     [SUBGOAL_THEN `&1 <= t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
        ASM_REWRITE_TAC[ARITH_EQ; REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `x / s <= &2 * log t /\ log t <= (t - inv t) / &2`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `x < &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `t <= &1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
        ASM_REWRITE_TAC[ARITH_EQ; REAL_POW_ONE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 * log t <= x / s /\ --log t <= (inv t - t) / &2`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_INV_1_LE]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[prove
       (`!a x:real. a / x = --a / --x`,
        REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG;
                    REAL_NEG_NEG])] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_NEG_GT0] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* ln n + 1/(n+1) < ln(n+1) < ln n + 1/n <= H_n <= ln n + 1 for n >= 1; the *)
(* first two links hold for every real n > 0. The bounds on H_n compare the  *)
(* sum with the integral of 1/x (REAL_SUM_INTEGRAL_[LU]BOUND_DECREASING).    *)
(* ------------------------------------------------------------------------- *)

let LOG_SUC_BOUNDS = prove
 (`!x. &0 < x
       ==> log x + inv(x + &1) < log(x + &1) /\ log(x + &1) < log x + inv x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `log(x + &1) = log x + log(&1 + inv x)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_MUL; REAL_LT_INV;
                 REAL_ARITH `&0 < y ==> &0 < &1 + y`] THEN
    AP_TERM_TAC THEN UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_LADD] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `inv(x:real)` LOG_GT_DIV) THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_LT_INV;
                 REAL_ARITH `&0 < y ==> -- &1 < y`] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a < c ==> b < c`) THEN
    UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC LOG_LT_STRONG THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_LT_INV;
                 REAL_ARITH `&0 < y ==> -- &1 < y`]]);;

let LOG_HARMONIC_BOUNDS = prove
 (`!n. 1 <= n
       ==> log(&n) + inv(&n + &1) < log(&n + &1) /\
           log(&n + &1) < log(&n) + inv(&n) /\
           log(&n) + inv(&n) <= sum(1..n) (\i. inv(&i)) /\
           sum(1..n) (\i. inv(&i)) <= log(&n) + &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n` (fun th -> REWRITE_TAC[MATCH_MP LOG_SUC_BOUNDS th])
  THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG; LOG_1; REAL_INV_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN real_interval[&1,&n]
        ==> (log has_real_derivative inv x)
            (atreal x within real_interval[&1,&n])`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. &1 <= x /\ x <= y ==> inv y <= inv x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `?m. n = m + 1 /\ 1 <= m`
     (X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`inv:real->real`; `log`; `1`; `m:num`]
                  REAL_SUM_INTEGRAL_LBOUND_DECREASING) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_ADD]) THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD; LOG_1] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a - &0 <= s ==> a + b <= s + b`) THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`inv:real->real`; `log`; `2`; `n:num`]
                  REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n /\ ~(n = 1) ==> 2 <= n`] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LOG_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `s <= a - &0 ==> &1 + s <= a + &1`) THEN
    FIRST_X_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* |ln x| <= |x - 1/x|/2 for x > 0, ln(x + y) <= ln x + y/x for x > 0 and   *)
(* x + y > 0, and ln x <= y (x^(1/y) - 1) for x, y > 0.                      *)
(* ------------------------------------------------------------------------- *)

let LOG_ABS_LE_HALF_DIFF_INV = prove
 (`!x. &0 < x ==> abs(log x) <= abs(x - inv x) / &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&1 <= x` THENL
   [MP_TAC(SPEC `x:real` LOG_LE_HALF_DIFF_INV) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_ARITH `&0 <= l ==> abs l = l`] THEN
    MP_TAC(SPEC `x:real` REAL_INV_LE_1) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `inv x:real` LOG_LE_HALF_DIFF_INV) THEN
    ASM_SIMP_TAC[LOG_INV; REAL_INV_INV] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inv x:real` REAL_INV_1_LE) THEN
    MP_TAC(SPEC `x:real` LOG_POS) THEN
    MP_TAC(SPECL [`x:real`; `&1`] LOG_MONO_LE_IMP) THEN
    ASM_REWRITE_TAC[LOG_1] THEN ASM_REAL_ARITH_TAC]);;

let LOG_ADD_LE_DIV = prove
 (`!x y. &0 < x /\ &0 < x + y ==> log(x + y) <= log x + y / x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x + y = x * (&1 + y / x)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + y / x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < x ==> &1 + y / x = (x + y) / x`;
                 REAL_LT_DIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_LE_LADD; LOG_LE_STRONG]);;

let LOG_LE_RPOW_ROOT = prove
 (`!x y. &0 < x /\ &0 < y ==> log x <= y * (x rpow (&1 / y) - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x rpow (&1 / y) - &1` LOG_LE_STRONG) THEN
  ASM_SIMP_TAC[REAL_SUB_ADD2; RPOW_POS_LT; LOG_RPOW] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `log x = y * (&1 / y * log x)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let LOG_BOUNDS_MISC = prove
 (`!x y. &0 < x /\ &0 < y
         ==> abs(log x) <= abs(x - inv x) / &2 /\
             log(x + y) <= log x + y / x /\
             log x <= y * (x rpow (&1 / y) - &1)`,
  SIMP_TAC[LOG_ABS_LE_HALF_DIFF_INV; LOG_ADD_LE_DIV; LOG_LE_RPOW_ROOT;
           REAL_LT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* ln(1+x) >= x - x^2/2 for x >= 0 and ln(1+x) >= x - x^2 for x >= -0.68.    *)
(* At x = -0.68 the bound reduces to ln(25/8) <= 1.1424, which follows from  *)
(* REAL_EXP_GE_PARTIAL_SUM_POW (degree 3, n = 8) by exact rational           *)
(* arithmetic.                                                               *)
(* ------------------------------------------------------------------------- *)

let LOG_GE_X_SUB_SQUARE = prove
 (`!x. -- &68 / &100 <= x ==> x - x pow 2 <= log(&1 + x)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN
   `!y. -- &1 < y
        ==> ((\x. log(&1 + x) - (x - x pow 2)) has_real_derivative
             y * (&1 + &2 * y) / (&1 + y)) (atreal y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `-- &1 < y` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `-- &1 / &2 <= x` THENL
   [MP_TAC(ISPECL [`\x. log(&1 + x) - (x - x pow 2)`;
                   `\y. y * (&1 + &2 * y) / (&1 + y)`;
                   `{x:real | -- &1 / &2 <= x}`; `&0`; `x:real`]
                  REAL_DERIVATIVE_SIGN_MINIMUM) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= --a ==> a <= &0`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. log(&1 + x) - (x - x pow 2)`;
                 `\y. y * (&1 + &2 * y) / (&1 + y)`;
                 `{x:real | -- &68 / &100 <= x /\ x <= -- &1 / &2}`;
                 `-- &68 / &100`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --y * --z ==> &0 <= y * z`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC]];
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a <= b ==> &0 <= b`) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ARITH `&0 <= l - c <=> c <= l`] THEN
  SUBGOAL_THEN `&8 / &25 = inv(&25 / &8)` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[LOG_INV; REAL_ARITH `&0 < &25 / &8`] THEN
  MATCH_MP_TAC(REAL_ARITH `l <= &714 / &625 ==> -- &714 / &625 <= --l`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..3) (\k. ((&714 / &625) / &8) pow k / &(FACT k)) pow 8` THEN
  CONJ_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV THENC DEPTH_CONV BETA_CONV THENC
             DEPTH_CONV NUM_FACT_CONV THENC REAL_RAT_REDUCE_CONV);
    MATCH_MP_TAC REAL_EXP_GE_PARTIAL_SUM_POW THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let LOG_GE_X_SUB_HALF_SQUARE = prove
 (`!x. &0 <= x ==> x - x pow 2 / &2 <= log(&1 + x)`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. log(&1 + x) - (x - x pow 2 / &2)`;
                 `\y. y pow 2 / (&1 + y)`; `{x:real | &0 <= x}`;
                 `&0`; `x:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
  DISCH_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= y` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC]);;

let LOG_QUADRATIC_LOWER = prove
 (`!x. (&0 <= x ==> x - x pow 2 / &2 <= log(&1 + x)) /\
       (-- &68 / &100 <= x ==> x - x pow 2 <= log(&1 + x))`,
  SIMP_TAC[LOG_GE_X_SUB_HALF_SQUARE; LOG_GE_X_SUB_SQUARE]);;

(* ------------------------------------------------------------------------- *)
(* 3.14 < pi < 3.1416, so on [0, pi/2] we have x^2 <= 8/3 and cos x >= 0.    *)
(* ------------------------------------------------------------------------- *)

let PI_BOUNDS_3927 = prove
 (`&157 / &50 < pi /\ pi < &3927 / &1250`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REAL_ARITH_TAC);;

let HALF_PI_SQUARE_COS_POS = prove
 (`!x. &0 <= x /\ x <= pi / &2 ==> x pow 2 <= &8 / &3 /\ &0 <= cos x`,
  REPEAT STRIP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&3927 / &2500) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC PI_BOUNDS_3927 THEN
      ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC COS_POS_PI_LE THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* x - x^3/2 <= x cos x <= x cos x / (1 - x^2/3) <= x cbrt(cos x)            *)
(*   <= x - x^3/6 <= x cos(x / sqrt 3) <= sin x for x in [0, pi/2].          *)
(* ------------------------------------------------------------------------- *)

let TRIG_PADE_LE_CUBE_ROOT = prove
 (`!x. &0 <= x /\ x <= pi / &2
       ==> x * cos x / (&1 - x pow 2 / &3) <= x * root 3 (cos x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` HALF_PI_SQUARE_COS_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - x pow 2 / &3` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cos x pow 2 <= (&1 - x pow 2 / &3) pow 3` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&1 - x pow 2 / &2 + x pow 4 / &24) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
        (SPECL [`1`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
      REAL_ARITH_TAC;
      MP_TAC(SPECL [`(x:real) pow 6`; `&8 - &3 * x pow 2`] REAL_LE_MUL) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_RING `(x:real) pow 6 = (x pow 3) pow 2`;
                    REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`3`; `cos x`] REAL_POW_ROOT) THEN
  REWRITE_TAC[ARITH_ODD; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= root 3 (cos x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ROOT_RPOW; ARITH_EQ; RPOW_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC `root 3 (cos x) pow 3 = cos x` THEN
  UNDISCH_TAC `&0 <= root 3 (cos x)` THEN
  UNDISCH_TAC `cos x pow 2 <= (&1 - x pow 2 / &3) pow 3` THEN
  UNDISCH_TAC `&0 < &1 - x pow 2 / &3` THEN
  SPEC_TAC(`&1 - x pow 2 / &3`,`d:real`) THEN
  SPEC_TAC(`root 3 (cos x)`,`t:real`) THEN
  SPEC_TAC(`cos x`,`c:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(t:real) pow 2 <= d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `3` THEN
    ASM_SIMP_TAC[ARITH_EQ; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `((t:real) pow 3) pow 2 <= d pow 3` THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(t:real) pow 3 = t * t pow 2`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let TRIG_CUBE_ROOT_LE_CUBIC = prove
 (`!x. &0 <= x /\ x <= pi / &2 ==> x * root 3 (cos x) <= x - x pow 3 / &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` HALF_PI_SQUARE_COS_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `x - x pow 3 / &6 = x * (&1 - x pow 2 / &6)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`3`; `root 3 (cos x)`; `&1 - x pow 2 / &6`]
                REAL_POW_LE2_ODD_EQ) THEN
  REWRITE_TAC[ARITH_ODD; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`3`; `cos x`] REAL_POW_ROOT) THEN
  REWRITE_TAC[ARITH_ODD; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC REAL_LE_TRANS `&1 - x pow 2 / &2 + x pow 4 / &24` THEN
  CONJ_TAC THENL
   [MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
      (SPECL [`1`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(x:real) pow 4`; `&9 - x pow 2`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_RING `(x:real) pow 4 = (x pow 2) pow 2`;
                REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let TRIG_CUBIC_LE_COS_SQRT3 = prove
 (`!x. &0 <= x ==> x - x pow 3 / &6 <= x * cos(x / sqrt(&3))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `x - x pow 3 / &6 = x * (&1 - x pow 2 / &6)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT1(EXPAND_PARTIAL_SUM_RULE
    (SPECL [`0`; `x / sqrt(&3)`] COS_TAYLOR_BOUNDS))) THEN
  MATCH_MP_TAC(REAL_ARITH
   `a / &2 = b ==> &1 + --(a / &2) <= c ==> &1 - b <= c`) THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS] THEN REAL_ARITH_TAC);;

let TRIG_COS_SQRT3_LE_SIN = prove
 (`!x. &0 <= x /\ x pow 2 <= &8 / &3 ==> x * cos(x / sqrt(&3)) <= sin x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x / sqrt(&3)) pow 2 = x pow 2 / &3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN SIMP_TAC[SQRT_POW_2; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
    (SPECL [`1`; `x / sqrt(&3)`] COS_TAYLOR_BOUNDS))) THEN
  REWRITE_TAC[REAL_RING `(y:real) pow 4 = (y pow 2) pow 2`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `x * (&1 - (x pow 2 / &3) / &2 + (x pow 2 / &3) pow 2 / &24)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `x - x pow 3 / &6 + x pow 5 / &120 - x pow 7 / &5040` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(EXPAND_PARTIAL_SUM_RULE
             (SPECL [`1`; `x:real`] SIN_TAYLOR_BOUNDS)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`x:real`; `5`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`(x:real) pow 5`; `&8 / &3 - x pow 2`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= (x:real) pow 5` THEN CONV_TAC REAL_ARITH);;

let TRIGONOMETRIC_BOUNDS = prove
 (`!x. &0 <= x /\ x <= pi / &2
       ==> x - x pow 3 / &2 <= x * cos x /\
           x * cos x <= x * cos x / (&1 - x pow 2 / &3) /\
           x * cos x / (&1 - x pow 2 / &3) <= x * root 3 (cos x) /\
           x * root 3 (cos x) <= x - x pow 3 / &6 /\
           x - x pow 3 / &6 <= x * cos(x / sqrt(&3)) /\
           x * cos(x / sqrt(&3)) <= sin x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` HALF_PI_SQUARE_COS_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TRIG_PADE_LE_CUBE_ROOT; TRIG_CUBE_ROOT_LE_CUBIC;
               TRIG_CUBIC_LE_COS_SQRT3; TRIG_COS_SQRT3_LE_SIN] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x - x pow 3 / &2 = x * (&1 - x pow 2 / &2)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1(EXPAND_PARTIAL_SUM_RULE
      (SPECL [`0`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < &1 - x pow 2 / &3 /\ &1 - x pow 2 / &3 <= &1`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* cosh(3927/2500) <= 63/25, by exact rational arithmetic from              *)
(* REAL_EXP_LE_RATIO_POW (n = 32) and REAL_EXP_GE_PARTIAL_SUM_POW (degree 3, *)
(* n = 8).                                                                   *)
(* ------------------------------------------------------------------------- *)

let COSH_3927_2500_LE = prove
 (`(exp(&3927 / &2500) + inv(exp(&3927 / &2500))) / &2 <= &63 / &25`,
  MP_TAC(SPECL [`32`; `&3927 / &2500`] REAL_EXP_LE_RATIO_POW) THEN
  MP_TAC(SPECL [`3`; `8`; `&3927 / &2500`] REAL_EXP_GE_PARTIAL_SUM_POW) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV THENC DEPTH_CONV BETA_CONV THENC
           DEPTH_CONV NUM_FACT_CONV THENC
           ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(prove
   (`!a b e c. &0 < a /\ (b + inv a) / &2 <= c
               ==> a <= e ==> e <= b ==> (e + inv e) / &2 <= c`,
    REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`; `e:real`] REAL_LE_INV2) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* x cos x <= x^3 / sinh^2 x <= x cos^2(x/2) <= sin x <= (x cos x + 2x)/3    *)
(*   <= x^2 / sinh x for x in [0, pi/2]; at x = 0 every term is 0, with      *)
(* x / 0 = 0, which is also the limit there. Some                           *)
(* links hold on larger ranges: x cos^2(x/2) <= sin x on [0, pi] and Cusa's  *)
(* sin x <= (x cos x + 2x)/3 for all x >= 0.                                 *)
(* ------------------------------------------------------------------------- *)

let MUL_COS_LE_SIN_SMALL = prove
 (`!y. &0 <= y /\ y pow 2 <= &8 ==> y * cos y <= sin y`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `y * (&1 - y pow 2 / &2 + y pow 4 / &24)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
      (SPECL [`1`; `y:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `y - y pow 3 / &6` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(EXPAND_PARTIAL_SUM_RULE
             (SPECL [`0`; `y:real`] SIN_TAYLOR_BOUNDS)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`y:real`; `3`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`(y:real) pow 3`; `&8 - y pow 2`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let MUL_COS_LE_SIN = prove
 (`!y. &0 <= y /\ y <= pi ==> y * cos y <= sin y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y <= pi / &2` THENL
   [MATCH_MP_TAC MUL_COS_LE_SIN_SMALL THEN
    MP_TAC(SPEC `y:real` HALF_PI_SQUARE_COS_POS) THEN
    ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos y <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `cos y = --cos(y - pi)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COS_PERIODIC_PI] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> --c <= &0`) THEN
    MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real` SIN_POS_PI_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= y * --cos y` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let MUL_COS_HALF_SQUARE_LE_SIN = prove
 (`!x. &0 <= x /\ x <= pi ==> x * cos(x / &2) pow 2 <= sin x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sin x = &2 * sin(x / &2) * cos(x / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SIN_DOUBLE] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x * cos(x / &2) pow 2 = &2 * ((x / &2) * cos(x / &2)) * cos(x / &2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cos(x / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MUL_COS_LE_SIN THEN ASM_REAL_ARITH_TAC);;

let SIN_LE_CUSA_SMALL = prove
 (`!x. &0 <= x /\ x pow 2 <= &12 ==> sin x <= (x * cos x + &2 * x) / &3`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `x - x pow 3 / &6 + x pow 5 / &120` THEN
  CONJ_TAC THENL
   [MP_TAC(EXPAND_PARTIAL_SUM_RULE
             (SPECL [`1`; `x:real`] SIN_TAYLOR_BOUNDS)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(x * (&1 - x pow 2 / &2 + x pow 4 / &24 - x pow 6 / &720) + &2 * x) /
    &3` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`x:real`; `5`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`(x:real) pow 5`; `&12 - x pow 2`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> (a + c) / &3 <= (b + c) / &3`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(CONJUNCT1(EXPAND_PARTIAL_SUM_RULE
      (SPECL [`1`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC]);;

let SIN_LE_CUSA = prove
 (`!x. &0 <= x ==> sin x <= (x * cos x + &2 * x) / &3`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x pow 2 <= &12` THEN
  ASM_SIMP_TAC[SIN_LE_CUSA_SMALL] THEN
  SUBGOAL_THEN `&3 <= x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x pow 2 <= &12)` THEN REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `(&3) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` SIN_BOUND) THEN MP_TAC(SPEC `x:real` COS_BOUND) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= x * (cos x + &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let COS_MUL_SINH_SQUARE_LE = prove
 (`!x. abs x <= &3927 / &2500
       ==> cos x * ((exp x - inv(exp x)) / &2) pow 2 <= x pow 2`,
  SUBGOAL_THEN
   `!x. &0 <= x /\ x <= &3927 / &2500
        ==> cos x * ((exp x - inv(exp x)) / &2) pow 2 <= x pow 2`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real`);
      FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`)] THEN
    REWRITE_TAC[COS_NEG; SINH_NEG; REAL_NEG_NEG; REAL_POW_NEG; ARITH] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC])] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `cos x <= &0` THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= &0 /\ &0 <= b ==> a <= b`) THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_ARITH `c * s <= &0 <=> &0 <= --c * s`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 <= &15421329 / &6250000` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&3927 / &2500) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(exp x - inv(exp x)) / &2 <=
    x + x pow 3 / &6 + x pow 5 / &120 + &63 / &25 * x pow 7 / &5040`
  ASSUME_TAC THENL
   [MP_TAC(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`2`; `&3927 / &2500`; `&63 / &25`; `x:real`]
            SINH_TAYLOR_UPPER)) THEN
    ASM_REWRITE_TAC[COSH_3927_2500_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos x <= &1 - x pow 2 / &2 + x pow 4 / &24` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`1`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_X_SINH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `(&1 - x pow 2 / &2 + x pow 4 / &24) *
    (x + x pow 3 / &6 + x pow 5 / &120 + &63 / &25 * x pow 7 / &5040)
    pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_POW_2] THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL [t; `&15421329 / &6250000 - x pow 2`]
                                   REAL_LE_MUL) THEN
                      ANTS_TAC THENL
                       [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
                        DISCH_TAC])
   [`(x:real) pow 4`; `(x:real) pow 6`; `(x:real) pow 8`; `(x:real) pow 10`;
    `(x:real) pow 12`; `(x:real) pow 14`; `(x:real) pow 16`] THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL [`x:real`; t] REAL_POW_LE) THEN
                      ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [`4`; `6`; `8`] THEN
  ASM_REAL_ARITH_TAC);;

let SINH_MUL_COS_HALF_GE = prove
 (`!x. &0 <= x /\ x <= &3927 / &2500
       ==> x <= (exp x - inv(exp x)) / &2 * cos(x / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x pow 2 <= &15421329 / &6250000` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&3927 / &2500) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 - x pow 2 / &8 + x pow 4 / &384 - x pow 6 / &46080 <= cos(x / &2)`
  MP_TAC THENL
   [MP_TAC(CONJUNCT1(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`1`; `x / &2`] COS_TAYLOR_BOUNDS))) THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x + x pow 3 / &6 + x pow 5 / &120 <= (exp x - inv(exp x)) / &2`
  MP_TAC THENL
   [MP_TAC(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`2`; `x:real`] SINH_TAYLOR_LOWER)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `(x + x pow 3 / &6 + x pow 5 / &120) *
    (&1 - x pow 2 / &8 + x pow 4 / &384 - x pow 6 / &46080)` THEN
  CONJ_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(SPECL [t; `&15421329 / &6250000 - x pow 2`]
                                     REAL_LE_MUL) THEN
                        ANTS_TAC THENL
                         [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
                          DISCH_TAC])
     [`(x:real) pow 3`; `(x:real) pow 5`; `(x:real) pow 7`;
      `(x:real) pow 9`] THEN
    MP_TAC(SPECL [`x:real`; `9`] REAL_POW_LE) THEN
    MP_TAC(SPECL [`x:real`; `3`] REAL_POW_LE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`x:real`; `3`] REAL_POW_LE) THEN
      MP_TAC(SPECL [`x:real`; `5`] REAL_POW_LE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(SPECL [t; `&15421329 / &6250000 - x pow 2`]
                                     REAL_LE_MUL) THEN
                        ANTS_TAC THENL
                         [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
                          DISCH_TAC])
     [`(x:real) pow 2`; `(x:real) pow 4`] THEN
    MP_TAC(SPECL [`x:real`; `4`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REAL_ARITH_TAC]);;

let SINH_MUL_COS_ADD_2_LE = prove
 (`!x. &0 <= x /\ x <= &3927 / &2500
       ==> (exp x - inv(exp x)) / &2 * (cos x + &2) <= &3 * x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x pow 2 <= &15421329 / &6250000` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&3927 / &2500) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(exp x - inv(exp x)) / &2 <=
    x + x pow 3 / &6 + x pow 5 / &120 + &63 / &25 * x pow 7 / &5040`
  ASSUME_TAC THENL
   [MP_TAC(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`2`; `&3927 / &2500`; `&63 / &25`; `x:real`]
            SINH_TAYLOR_UPPER)) THEN
    ASM_REWRITE_TAC[COSH_3927_2500_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos x <= &1 - x pow 2 / &2 + x pow 4 / &24` MP_TAC THENL
   [MP_TAC(CONJUNCT2(EXPAND_PARTIAL_SUM_RULE
     (SPECL [`1`; `x:real`] COS_TAYLOR_BOUNDS))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_X_SINH) THEN
  MP_TAC(SPEC `x:real` COS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `(x + x pow 3 / &6 + x pow 5 / &120 + &63 / &25 * x pow 7 / &5040) *
    ((&1 - x pow 2 / &2 + x pow 4 / &24) + &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL [t; `&15421329 / &6250000 - x pow 2`]
                                   REAL_LE_MUL) THEN
                      ANTS_TAC THENL
                       [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
                        DISCH_TAC])
   [`(x:real) pow 5`; `(x:real) pow 7`; `(x:real) pow 9`] THEN
  MP_TAC(SPECL [`x:real`; `5`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

let HYPERBOLIC_SINH_BOUNDS = prove
 (`!x. &0 <= x /\ x <= pi / &2
       ==> x * cos x <= x pow 3 / ((exp x - inv(exp x)) / &2) pow 2 /\
           x pow 3 / ((exp x - inv(exp x)) / &2) pow 2
           <= x * cos(x / &2) pow 2 /\
           x * cos(x / &2) pow 2 <= sin x /\
           sin x <= (x * cos x + &2 * x) / &3 /\
           (x * cos x + &2 * x) / &3 <= x pow 2 / ((exp x - inv(exp x)) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` HALF_PI_SQUARE_COS_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x <= &3927 / &2500 /\ x <= pi` STRIP_ASSUME_TAC THENL
   [MP_TAC PI_BOUNDS_3927 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MUL_COS_HALF_SQUARE_LE_SIN; SIN_LE_CUSA] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_EXP_0; REAL_INV_1; REAL_SUB_REFL; COS_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ abs x <= &3927 / &2500` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` COS_MUL_SINH_SQUARE_LE) THEN
  MP_TAC(SPEC `x:real` SINH_MUL_COS_HALF_GE) THEN
  MP_TAC(SPEC `x:real` SINH_MUL_COS_ADD_2_LE) THEN
  MP_TAC(SPEC `x:real` REAL_LE_X_SINH) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`(exp x - inv(exp x)) / &2`,`s:real`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s /\ &0 < s pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`x:real`; `cos x * s pow 2`; `(x:real) pow 2`]
                 REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MP_TAC(SPECL [`2`; `x:real`; `s * cos(x / &2)`] REAL_POW_LE2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`x:real`; `(x:real) pow 2`; `(s * cos(x / &2)) pow 2`]
                 REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MP_TAC(SPECL [`x / &3`; `s * (cos x + &2)`; `&3 * x`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* max{2/pi, (pi^2 - x^2)/(pi^2 + x^2)} <= sin x / x <= cos(x/2) <= 1        *)
(*   <= 1 + x^2/3 <= tan x / x for x in (0, pi/2], the last link for         *)
(* x < pi/2 where tan is defined; and the non-trivial bounds multiplied by x *)
(* on the closed interval. Jordan's 2/pi <= sin x / x holds because sin x / x*)
(* decreases; Redheffer's bound follows from the degree-7 Taylor bound on    *)
(* sin and 3.14 < pi < 3.1416.                                               *)
(* ------------------------------------------------------------------------- *)

let TAN_GE_CUBIC = prove
 (`!x. &0 <= x /\ x < pi / &2 ==> x + x pow 3 / &3 <= tan x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL [`\x. tan x - (x + x pow 3 / &3)`;
                 `\x. tan x pow 2 - x pow 2`;
                 `{x:real | &0 <= x /\ x < pi / &2}`; `&0`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL; TAN_0] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
  STRIP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    MP_TAC(SPEC `y:real` TAN_ABS_GE_X) THEN
    MP_TAC(SPEC `y:real` TAN_POS_PI2_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 < cos y` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[tan] THEN MP_TAC(SPEC `y:real` SIN_CIRCLE) THEN
  UNDISCH_TAC `&0 < cos y` THEN CONV_TAC REAL_FIELD);;

let SIN_DIV_GE_JORDAN = prove
 (`!x. &0 < x /\ x <= pi / &2 ==> &2 / pi <= sin x / x`,
  REPEAT STRIP_TAC THEN MP_TAC PI_POS THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. --(sin x / x)`;
                 `\y. (sin y - y * cos y) / y pow 2`;
                 `{x:real | &0 < x /\ x <= pi / &2}`; `x:real`; `pi / &2`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; SIN_PI2] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_SUB_LE] THEN
      MATCH_MP_TAC MUL_COS_LE_SIN THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> --s <= --a ==> b <= s`) THEN
  UNDISCH_TAC `&0 < pi` THEN CONV_TAC REAL_FIELD);;

let SIN_DIV_GE_REDHEFFER = prove
 (`!x. &0 < x /\ x <= pi / &2
       ==> (pi pow 2 - x pow 2) / (pi pow 2 + x pow 2) <= sin x / x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` HALF_PI_SQUARE_COS_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC PI_BOUNDS_3927 THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `&1 - x pow 2 / &6 + x pow 4 / &120 - x pow 6 / &5040` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MP_TAC(EXPAND_PARTIAL_SUM_RULE
             (SPECL [`1`; `x:real`] SIN_TAYLOR_BOUNDS)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN `&0 < pi pow 2 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 < pi pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN
   `(&157 / &50) pow 2 <= pi pow 2 /\ pi pow 2 <= (&3927 / &1250) pow 2`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)] THEN
  UNDISCH_TAC `x pow 2 <= &8 / &3` THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_RING `(x:real) pow 4 = (x pow 2) pow 2`;
              REAL_RING `(x:real) pow 6 = (x pow 2) pow 3`] THEN
  SPEC_TAC(`(x:real) pow 2`,`u:real`) THEN SPEC_TAC(`pi pow 2`,`p:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL t REAL_LE_MUL) THEN
                      ANTS_TAC THENL
                       [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
                        DISCH_TAC])
   [[`u:real`; `&15421329 / &1562500 - p`];
    [`(u:real) pow 2`; `p - &24649 / &2500`];
    [`u:real`; `&8 / &3 - u`];
    [`(u:real) pow 3`; `&15421329 / &1562500 - p`];
    [`(u:real) pow 2`; `&8 / &3 - u`];
    [`(u:real) pow 3`; `&8 / &3 - u`]] THEN
  MP_TAC(SPECL [`u:real`; `3`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

let SIN_LE_MUL_COS_HALF = prove
 (`!x. &0 <= x /\ x <= pi ==> sin x <= x * cos(x / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sin x = &2 * sin(x / &2) * cos(x / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SIN_DOUBLE] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cos(x / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `x / &2` REAL_ABS_SIN_BOUND_LE) THEN ASM_REAL_ARITH_TAC);;

let SIN_DIV_BOUNDS = prove
 (`!x. &0 < x /\ x <= pi / &2
       ==> max (&2 / pi) ((pi pow 2 - x pow 2) / (pi pow 2 + x pow 2))
           <= sin x / x /\
           sin x / x <= cos(x / &2) /\
           cos(x / &2) <= &1 /\
           &1 <= &1 + x pow 2 / &3 /\
           (x < pi / &2 ==> &1 + x pow 2 / &3 <= tan x / x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_MAX_LE; SIN_DIV_GE_JORDAN; SIN_DIV_GE_REDHEFFER] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC SIN_LE_MUL_COS_HALF THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x / &2` COS_BOUND) THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MP_TAC(SPEC `x:real` TAN_GE_CUBIC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let SIN_MUL_BOUNDS = prove
 (`!x. &0 <= x /\ x <= pi / &2
       ==> x * max (&2 / pi) ((pi pow 2 - x pow 2) / (pi pow 2 + x pow 2))
           <= sin x /\
           sin x <= x * cos(x / &2) /\
           (x < pi / &2 ==> x + x pow 3 / &3 <= tan x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TAN_GE_CUBIC] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC SIN_LE_MUL_COS_HALF THEN ASM_REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[SIN_0; REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` SIN_DIV_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2 sqrt(x+1) - 2 sqrt x < 1/sqrt x < sqrt(x+1) - sqrt(x-1)                 *)
(*   < 2 sqrt x - 2 sqrt(x-1) for x >= 1; the first link holds for every     *)
(* x > 0.                                                                    *)
(* ------------------------------------------------------------------------- *)

let SQRT_DIFFERENCE_BOUNDS = prove
 (`!x. &0 < x
       ==> &2 * sqrt(x + &1) - &2 * sqrt x < inv(sqrt x) /\
           (&1 <= x
            ==> inv(sqrt x) < sqrt(x + &1) - sqrt(x - &1) /\
                sqrt(x + &1) - sqrt(x - &1) <
                &2 * sqrt x - &2 * sqrt(x - &1))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * sqrt(x + &1) - &2 * sqrt x < inv(sqrt x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sqrt x pow 2 = x /\ sqrt(x + &1) pow 2 = x + &1 /\
      &0 < sqrt x /\ &0 <= sqrt(x + &1)`
    MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; SQRT_POS_LE; REAL_LT_IMP_LE;
                   REAL_ARITH `&0 < x ==> &0 <= x + &1`];
      ALL_TAC] THEN
    SPEC_TAC(`sqrt(x + &1)`,`c:real`) THEN SPEC_TAC(`sqrt x`,`b:real`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(b:real) < c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(c:real) pow 2 <= b pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `inv(b:real) = &1 / b`] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 < (c - b:real) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(b:real) pow 2 = x` THEN
    UNDISCH_TAC `(c:real) pow 2 = x + &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sqrt(x - &1) pow 2 = x - &1 /\ sqrt x pow 2 = x /\
    sqrt(x + &1) pow 2 = x + &1 /\ &0 <= sqrt(x - &1) /\
    &0 <= sqrt x /\ &0 <= sqrt(x + &1)`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 <= x - &1 /\ &0 <= x /\ &0 <= x + &1`
    STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]];
    ALL_TAC] THEN
  SPEC_TAC(`sqrt(x + &1)`,`c:real`) THEN SPEC_TAC(`sqrt x`,`b:real`) THEN
  SPEC_TAC(`sqrt(x - &1)`,`a:real`) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) < b /\ b < c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(b:real) pow 2 <= a pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(c:real) pow 2 <= b pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `b pow 2 < &1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) * c < x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real) pow 2 <= (a * c) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c + a < &2 * b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&2 * b) pow 2 <= (c + a) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH
       `(&2 * b) pow 2 = &4 * b pow 2 /\
        (c + a:real) pow 2 = c pow 2 + a pow 2 + &2 * (a * c)`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `inv(b:real) = &1 / b`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ;
               REAL_ARITH `&1 <= b ==> &0 < b`] THEN
  SUBGOAL_THEN `&0 < (c - b) pow 2 /\ &0 < (c - a) * (&2 * b - (c + a))`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(a:real) pow 2 = x - &1` THEN
  UNDISCH_TAC `(b:real) pow 2 = x` THEN
  UNDISCH_TAC `(c:real) pow 2 = x + &1` THEN
  UNDISCH_TAC `c + a < &2 * (b:real)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* x <= (x+1)/2 - (x-1)^2/2 <= sqrt x <= (x+1)/2 - (x-1)^2/8 for x in [0,1]; *)
(* the middle link holds for every x >= 0.                                   *)
(* ------------------------------------------------------------------------- *)

let SQRT_QUADRATIC_BOUNDS = prove
 (`!x. &0 <= x
       ==> (x <= &1 ==> x <= (x + &1) / &2 - (x - &1) pow 2 / &2) /\
           (x + &1) / &2 - (x - &1) pow 2 / &2 <= sqrt x /\
           (x <= &1 ==> sqrt x <= (x + &1) / &2 - (x - &1) pow 2 / &8)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` SQRT_POW_2) THEN MP_TAC(SPEC `x:real` SQRT_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x <= &1 ==> sqrt x <= &1` MP_TAC THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM SQRT_1] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`sqrt x`,`s:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `&0 <= s * (s - &1) pow 2 * (s + &2)` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s pow 2 * (&1 - s pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_SUB_LE];
      REAL_ARITH_TAC];
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - s) pow 3 * (s + &3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_SUB_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;
