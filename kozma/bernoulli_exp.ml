(* ========================================================================= *)
(* Bernoulli's inequality and bounds on the exponential function, from      *)
(* L. Kozma, "Useful Inequalities" (v0.44).                                  *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* The tangent line of the power function t |-> t rpow r at t = 1: it lies   *)
(* below the graph when the function is convex (r >= 1 or r <= 0) and above  *)
(* it when the function is concave (0 <= r <= 1); for 0 < r < 1 the reverse  *)
(* inequality is strict at every t >= 0 other than t = 1.                    *)
(* ------------------------------------------------------------------------- *)

let RPOW_BERNOULLI_TANGENT = prove
 (`!r t. &1 <= r /\ &0 <= t \/ r <= &0 /\ &0 < t
         ==> &1 + r * (t - &1) <= t rpow r`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`\x:real. x rpow r`; `r:real`; `{x:real | &0 <= x}`;
                   `&1`; `t:real`] REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP);
    MP_TAC(ISPECL [`\x:real. x rpow r`; `r:real`; `{x:real | &0 < x}`;
                   `&1`; `t:real`] REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP)] THEN
  REWRITE_TAC[RPOW_ONE] THEN
  (ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC REAL_CONVEX_ON_RPOW THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC REAL_CONVEX_ON_RPOW_NEG THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[SUBSET; IN_REAL_SEGMENT; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  MP_TAC(SPECL [`&1`; `r:real`] HAS_REAL_DERIVATIVE_RPOW) THEN
  REWRITE_TAC[REAL_LT_01; RPOW_ONE; REAL_MUL_RID]);;

let RPOW_BERNOULLI_TANGENT_REV = prove
 (`!r t. &0 <= r /\ r <= &1 /\ &0 <= t ==> t rpow r <= &1 + r * (t - &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[RPOW_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`inv(r:real)`; `(t:real) rpow r`] RPOW_BERNOULLI_TANGENT) THEN
  ASM_SIMP_TAC[RPOW_RPOW; RPOW_POS_LE; REAL_MUL_RINV; RPOW_POW;
               REAL_POW_1] THEN
  ANTS_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r * (&1 + inv r * ((t:real) rpow r - &1)) <= r * t`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC; REAL_MUL_RINV;
                 REAL_MUL_LID] THEN
    REAL_ARITH_TAC]);;

let RPOW_BERNOULLI_TANGENT_REV_STRICT = prove
 (`!r t. &0 < r /\ r < &1 /\ &0 <= t /\ ~(t = &1)
         ==> t rpow r < &1 + r * (t - &1)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` SQRT_POW_2) THEN MP_TAC(SPEC `t:real` SQRT_POS_LT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SPEC_TAC(`sqrt t`,`a:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(a pow 2) rpow r = (a rpow r) pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW; REAL_LT_IMP_LE] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `a:real`] RPOW_BERNOULLI_TANGENT_REV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  TRANS_TAC REAL_LET_TRANS `(&1 + r * (a - &1)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r * (&1 - r) * (a - &1) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_CASES_TAC `a = &1` THENL
     [UNDISCH_TAC `~(a pow 2 = &1)` THEN ASM_REWRITE_TAC[REAL_POW_ONE];
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bernoulli's inequality for real exponents, and its reverse. At x = -1 a   *)
(* negative exponent would need 0 to a negative power, so it is excluded.    *)
(* ------------------------------------------------------------------------- *)

let RPOW_BERNOULLI = prove
 (`!x r. -- &1 <= x /\ (r <= &0 \/ &1 <= r) /\ (x = -- &1 ==> &0 <= r)
         ==> &1 + r * x <= (&1 + x) rpow r`,
  REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x = -- &1` THENL
     [SUBGOAL_THEN `r = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[REAL_LE_ANTISYM];
        REWRITE_TAC[RPOW_0] THEN REAL_ARITH_TAC];
      MP_TAC(SPECL [`r:real`; `&1 + x`] RPOW_BERNOULLI_TANGENT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    MP_TAC(SPECL [`r:real`; `&1 + x`] RPOW_BERNOULLI_TANGENT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let RPOW_BERNOULLI_REV = prove
 (`!x r. -- &1 <= x /\ &0 <= r /\ r <= &1
         ==> (&1 + x) rpow r <= &1 + r * x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `&1 + x`] RPOW_BERNOULLI_TANGENT_REV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* (1 + x)^r <= 1 / (1 - r x) for x >= -1 and r x < 1, with r >= 0 or        *)
(* r <= -1. For r <= -1 the condition r x < 1 already forces x > -1.         *)
(* ------------------------------------------------------------------------- *)

let RPOW_BERNOULLI_INV = prove
 (`!x r. (r <= -- &1 \/ &0 <= r) /\ -- &1 <= x /\ r * x < &1
         ==> (&1 + x) rpow r <= inv(&1 - r * x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `&0 < &1 + x` ASSUME_TAC THENL
     [ASM_CASES_TAC `x = -- &1` THENL
       [UNDISCH_TAC `r * x < &1` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`--r:real`; `&1 + x`] RPOW_BERNOULLI_TANGENT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[RPOW_NEG] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x = -- &1` THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 + -- &1 = &0`; RPOW_ZERO] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_INV_1; REAL_LE_REFL;
                    REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`--r:real`; `&1 + x`] RPOW_BERNOULLI_TANGENT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* (1 + x)^r <= 1 + r x / (x + 1) for r in [-1, 0], for all x > -1.          *)
(* ------------------------------------------------------------------------- *)

let RPOW_BERNOULLI_NEG = prove
 (`!x r. -- &1 < x /\ -- &1 <= r /\ r <= &0
         ==> (&1 + x) rpow r <= &1 + r * x / (x + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + x) rpow r = inv(&1 + x) rpow (--r)` SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_INV; RPOW_NEG; REAL_INV_INV]; ALL_TAC] THEN
  MP_TAC(SPECL [`--r:real`; `inv(&1 + x)`] RPOW_BERNOULLI_TANGENT_REV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> u <= a ==> u <= b`) THEN
  UNDISCH_TAC `-- &1 < x` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The chord of the convex function (1 + x)^r between x = 0 and x = 1.       *)
(* ------------------------------------------------------------------------- *)

let RPOW_BERNOULLI_CHORD = prove
 (`!x r. &0 <= x /\ x <= &1 /\ (r <= &0 \/ &1 <= r)
         ==> (&1 + x) rpow r <= &1 + (&2 rpow r - &1) * x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(\t. t rpow r) real_convex_on {t | &0 < t}` MP_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MATCH_MP_TAC REAL_CONVEX_ON_RPOW_NEG;
      MATCH_MP_TAC REAL_CONVEX_ON_RPOW] THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_convex_on; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `&2`; `&1 - x`; `x:real`]) THEN
  ASM_REWRITE_TAC[RPOW_ONE] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b /\ c = d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* (1 + n x)^(n+1) >= (1 + (n+1) x)^n whenever (n+1) x >= -1, and for every *)
(* x when n is odd: if 1 + (n+1) x < 0 then (1 + (n+1) x)^n is negative      *)
(* while the other side is an even power.                                    *)
(* ------------------------------------------------------------------------- *)

let BERNOULLI_POW_SUC_LEMMA = prove
 (`!n a x. &0 <= a /\ &0 <= a + x
           ==> (a + x) pow n * (a - &n * x) <= a pow (n + 1)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_LID;
                ADD_CLAUSES; REAL_POW_1; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC; ADD_CLAUSES] THEN
  TRANS_TAC REAL_LE_TRANS `a * ((a + x) pow n * (a - &n * x))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= (a + x) pow n * ((&n + &1) * x pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_POW_2;
                   REAL_ARITH `&0 <= &n + &1`];
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[GSYM ADD1; real_pow]]);;

let BERNOULLI_POW_SUC = prove
 (`!n x. ODD n \/ -- &1 <= &(n + 1) * x
         ==> (&1 + &(n + 1) * x) pow n <= (&1 + &n * x) pow (n + 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `-- &1 <= &(n + 1) * x` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    TRANS_TAC REAL_LE_TRANS `&0` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(&0) pow SUC(2 * m)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2_ODD THEN
        REWRITE_TAC[ODD; NOT_ODD; EVEN_DOUBLE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_ZERO; NOT_SUC; REAL_LE_REFL]];
      REWRITE_TAC[ARITH_RULE `SUC(2 * m) + 1 = (m + 1) * 2`;
                  GSYM REAL_POW_POW; REAL_LE_POW_2]]] THEN
  MP_TAC(SPECL [`n:num`; `&1 + &n * x`; `x:real`]
               BERNOULLI_POW_SUC_LEMMA) THEN
  REWRITE_TAC[REAL_ARITH `(&1 + n * x) - n * x = &1`; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + n * x) + x = &1 + (n + &1) * x`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_ADD]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 <= &1 + y <=> -- &1 <= y`] THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> -- &1 <= y`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* (a + b)^n <= a^n + n b (a + b)^(n-1) for a >= 0 and a + b >= 0 (b may be  *)
(* negative).                                                                *)
(* ------------------------------------------------------------------------- *)

let BINOMIAL_POW_LE = prove
 (`!n a b:real. &0 <= a /\ &0 <= a + b
                ==> (a + b) pow n <= a pow n + &n * b * (a + b) pow (n - 1)`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; SUC_SUB1; GSYM REAL_OF_NUM_SUC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(a + b) * (a pow n + &n * b * (a + b:real) pow (n - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a + b) pow n = (a + b) * (a + b:real) pow (n - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b * a pow n <= b * (a + b) * (a + b:real) pow (n - 1)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= b \/ b <= &0`) THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH
       `(b:real) * x <= b * y <=> --b * y <= --b * x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

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
(* A differentiable function on an interval whose derivative is <= 0 left of *)
(* c and >= 0 right of c attains its minimum at c.                           *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Partial sums of the exponential series bound exp x from below, x >= 0.    *)
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
  SUBGOAL_THEN `sum (0..SUC n) (\k. &0 pow k / &(FACT k)) = &1`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT)
                         (ARITH_RULE `0 <= SUC n`)] THEN
    REWRITE_TAC[real_pow; FACT; REAL_DIV_1;
                REAL_ARITH `&1 + s = &1 <=> s = &0`] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    SIMP_TAC[REAL_POW_ZERO; ARITH_RULE `0 + 1 <= i ==> ~(i = 0)`;
             real_div; REAL_MUL_LZERO];
    REWRITE_TAC[REAL_EXP_0] THEN REAL_ARITH_TAC]);;

let REAL_EXP_CUBIC_LE = prove
 (`!y. &0 <= y ==> &1 + y + y pow 2 / &2 + y pow 3 / &6 <= exp y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`3`; `y:real`] REAL_EXP_PARTIAL_SUM_LE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG;
              FACT; LE_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_DIV_1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* e^x >= (1 + x/n)^n >= 1 + x and (1 + x/n)^n >= e^x (1 - x^2/n), for real  *)
(* n >= 1 and every x >= -n.                                                 *)
(* ------------------------------------------------------------------------- *)

let RPOW_ADD_DIV_LE_EXP = prove
 (`!x t. &0 < t /\ -- t <= x ==> (&1 + x / t) rpow t <= exp x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = --(t:real)` THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < t ==> &1 + --t / t = &0`; RPOW_ZERO;
                 REAL_LT_IMP_NZ; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + x / t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < t ==> &1 + x / t = (t + x) / t`] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rpow; REAL_EXP_MONO_LE] THEN
  TRANS_TAC REAL_LE_TRANS `(t:real) * x / t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[LOG_LE_STRONG; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_FIELD `&0 < t ==> t * x / t = x`; REAL_LE_REFL]]);;

let RPOW_ADD_DIV_GE_EXP_MUL = prove
 (`!n x. &1 <= n /\ -- n <= x
         ==> exp x * (&1 - x pow 2 / n) <= (&1 + x / n) rpow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + x / n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> &1 + x / n = (n + x) / n`] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 - x pow 2 / n <= &0` THENL
   [TRANS_TAC REAL_LE_TRANS `&0` THEN ASM_SIMP_TAC[RPOW_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= a * --b`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((x:real) / n) pow 2 <= x pow 2 / n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> (x / n) pow 2 = (x pow 2 / n) / n`;
                 REAL_LE_LDIV_EQ] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(x / n)) rpow n = exp(--x)` ASSUME_TAC THENL
   [REWRITE_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `((&1 + x / n) * exp(--(x / n))) rpow n * exp x` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[RPOW_MUL; GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD;
                    REAL_ADD_LINV; REAL_EXP_0; REAL_MUL_RID;
                    REAL_LE_REFL]] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  TRANS_TAC REAL_LE_TRANS `(&1 + --((x / n) pow 2)) rpow n` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`--((x / n) pow 2):real`; `n:real`] RPOW_BERNOULLI) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= c ==> b <= c`) THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(SPEC `--(x / n):real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(&1 + x / n) * (&1 + --(x / n))` THEN
  CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let REAL_EXP_RPOW_LIMIT_BOUNDS = prove
 (`!n x. &1 <= n /\ -- n <= x
         ==> &1 + x <= (&1 + x / n) rpow n /\
             (&1 + x / n) rpow n <= exp x /\
             exp x * (&1 - x pow 2 / n) <= (&1 + x / n) rpow n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_ADD_DIV_GE_EXP_MUL; RPOW_ADD_DIV_LE_EXP] THEN
  MP_TAC(SPECL [`(x:real) / n`; `n:real`] RPOW_BERNOULLI) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
                 REAL_FIELD `&0 < n ==> (x / n = -- &1 <=> x = --n)`] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= c ==> b <= c`) THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* x^n / n! + 1 <= e^x <= (1 + x/n)^(n + x/2) and e^x >= (e x / n)^n. The   *)
(* first link needs n to be a natural number; the others hold for real n.   *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_POW_FACT_LE = prove
 (`!n x. 1 <= n /\ &0 <= x ==> x pow n / &(FACT n) + &1 <= exp x`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `sum(0..n) (\k. x pow k / &(FACT k))` THEN
  ASM_SIMP_TAC[REAL_EXP_PARTIAL_SUM_LE] THEN
  REWRITE_TAC[MATCH_MP (SPEC_ALL SUM_CLAUSES_LEFT) (ARITH_RULE `0 <= n`)] THEN
  REWRITE_TAC[real_pow; FACT; REAL_DIV_1] THEN
  SUBGOAL_THEN `n = SUC(n - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `0 + 1 <= SUC m`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> t + &1 <= &1 + s + t`) THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]);;

let REAL_EXP_LE_RPOW_ADD_HALF = prove
 (`!n x. &0 < n /\ &0 <= x ==> exp x <= (&1 + x / n) rpow (n + x / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x / n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + x / n` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[rpow; REAL_EXP_MONO_LE] THEN
  TRANS_TAC REAL_LE_TRANS
   `(n + x / &2) * (&2 * (x / n) / (&2 + x / n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= x / n` THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[LOG_GE_DIV_HALF] THEN
    ASM_REAL_ARITH_TAC]);;

let RPOW_EXP_MUL_DIV_LE_EXP = prove
 (`!n x. &0 < n /\ &0 <= x ==> (exp(&1) * x / n) rpow n <= exp x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; RPOW_ZERO;
                 REAL_LT_IMP_NZ; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x / n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&1) * x / n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[rpow; REAL_EXP_MONO_LE; LOG_MUL; REAL_EXP_POS_LT; LOG_EXP] THEN
  MP_TAC(SPEC `(x:real) / n - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (u - &1) = u`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN TRANS_TAC REAL_LE_TRANS `n * (&1 + (x / n - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < n` THEN
    CONV_TAC REAL_FIELD]);;

let REAL_EXP_RPOW_DIV_BOUNDS = prove
 (`!n x. &0 < n /\ &0 <= x
         ==> exp x <= (&1 + x / n) rpow (n + x / &2) /\
             (exp(&1) * x / n) rpow n <= exp x`,
  SIMP_TAC[REAL_EXP_LE_RPOW_ADD_HALF; RPOW_EXP_MUL_DIV_LE_EXP]);;

(* ------------------------------------------------------------------------- *)
(* For x, y > 0: x^y + y^x > 1, e^x > (1 + x/y)^y > e^(xy/(x+y)) and         *)
(* x/y >= e^((x-y)/x). The sheet also states x^y > x/(x+y) for all x, y > 0, *)
(* which is false (x = 1/2, y = 4); it holds when y <= 1 or x >= 1.          *)
(* ------------------------------------------------------------------------- *)

let RPOW_GE_DIV_LEMMA = prove
 (`!x y. &0 < x /\ &0 <= y /\ y <= &1 ==> x / (x + y - x * y) <= x rpow y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x rpow y = x / x rpow (&1 - y)` SUBST1_TAC THENL
   [MP_TAC(SPECL [`x:real`; `&1`; `&1 - y`] RPOW_SUB) THEN
    ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_ARITH `&1 - (&1 - y) = y`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - y`; `x:real`] RPOW_BERNOULLI_TANGENT_REV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < x + y - x * y` ASSUME_TAC THENL
   [ASM_CASES_TAC `y = &1` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < x * (&1 - y)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[RPOW_POS_LT] THEN
  ASM_REAL_ARITH_TAC);;

let RPOW_GT_DIV_ADD = prove
 (`!x y. &0 < x /\ &0 < y /\ (y <= &1 \/ &1 <= x)
         ==> x / (x + y) < x rpow y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    DISJ_CASES_TAC)) THENL
   [TRANS_TAC REAL_LTE_TRANS `(x:real) / (x + y - x * y)` THEN
    ASM_SIMP_TAC[RPOW_GE_DIV_LEMMA; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < x + y - x * y /\ &0 < x * y` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= x * (&1 - y)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_MUL]];
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REAL_ARITH_TAC;
    TRANS_TAC REAL_LTE_TRANS `&1` THEN
    ASM_SIMP_TAC[RPOW_LE_1; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_ADD] THEN ASM_REAL_ARITH_TAC]);;

let RPOW_GT_DIV_ADD_COUNTEREXAMPLE = prove
 (`~(!x y. &0 < x /\ &0 < y ==> x / (x + y) < x rpow y)`,
  DISCH_THEN(MP_TAC o SPECL [`&1 / &2`; `&4`]) THEN
  REWRITE_TAC[RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let RPOW_ADD_RPOW_GT_1 = prove
 (`!x y. &0 < x /\ &0 < y ==> &1 < x rpow y + y rpow x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&1 <= x` THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] RPOW_LE_1) THEN
    MP_TAC(SPECL [`y:real`; `x:real`] RPOW_POS_LT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= y` THENL
   [MP_TAC(SPECL [`y:real`; `x:real`] RPOW_LE_1) THEN
    MP_TAC(SPECL [`x:real`; `y:real`] RPOW_POS_LT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `y:real`] RPOW_GT_DIV_ADD) THEN
  MP_TAC(SPECL [`y:real`; `x:real`] RPOW_GT_DIV_ADD) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `~(&1 <= x) ==> x <= &1`] THEN
  SUBGOAL_THEN `y / (y + x) + x / (x + y) = &1` MP_TAC THENL
   [UNDISCH_TAC `&0 < x` THEN UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC]);;

let REAL_EXP_RPOW_BOUNDS = prove
 (`!x y. &0 < x /\ &0 < y
         ==> (&1 + x / y) rpow y < exp x /\
             exp(x * y / (x + y)) < (&1 + x / y) rpow y /\
             exp((x - y) / x) <= x / y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x / y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + x / y) rpow y = exp(y * log(&1 + x / y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[rpow] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `(x:real) / y` LOG_LT_STRONG) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `x = (y:real) * x / y`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    MP_TAC(SPEC `(x:real) / y` LOG_GT_DIV) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `x * y / (x + y) = y * (x / y) / (&1 + x / y)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < x` THEN UNDISCH_TAC `&0 < y` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    MP_TAC(SPEC `(x:real) / y - &1` LOG_GE_DIV) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 + (u - &1) = u`] THEN
    SUBGOAL_THEN `(x / y - &1) / (x / y) = (x - y) / x` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < x` THEN UNDISCH_TAC `&0 < y` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `x / y = exp(log(x / y))`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [ASM_SIMP_TAC[EXP_LOG]; ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* 1/(2 - x) < x^x < x^2 - x + 1 for x in (0,1), and e^(2x) <= (1+x)/(1-x)   *)
(* for x in [0,1).                                                           *)
(* ------------------------------------------------------------------------- *)

let RPOW_SELF_BOUNDS = prove
 (`!x. &0 < x /\ x < &1
       ==> inv(&2 - x) < x rpow x /\ x rpow x < x pow 2 - x + &1`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `x rpow x = x / x rpow (&1 - x)` SUBST1_TAC THENL
     [MP_TAC(SPECL [`x:real`; `&1`; `&1 - x`] RPOW_SUB) THEN
      ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1;
                      REAL_ARITH `&1 - (&1 - x) = x`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&1 - x`; `x:real`] RPOW_BERNOULLI_TANGENT_REV_STRICT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < x rpow (&1 - x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN
     `inv(&2 - x) * x rpow (&1 - x) < inv(&2 - x) * x * (&2 - x)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `(b:real) = c ==> a < b ==> a < c`) THEN
      UNDISCH_TAC `x < &1` THEN CONV_TAC REAL_FIELD];
    MP_TAC(SPECL [`x:real`; `x:real`] RPOW_BERNOULLI_TANGENT_REV_STRICT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let REAL_EXP_DOUBLE_LE = prove
 (`!x. &0 <= x /\ x < &1 ==> exp(&2 * x) <= (&1 + x) / (&1 - x)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * x <= log(&1 + x) - log(&1 - x)` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    MP_TAC(ISPECL [`\x. (log(&1 + x) - log(&1 - x)) - &2 * x`;
                   `\y. &2 * y pow 2 / ((&1 + y) * (&1 - y))`;
                   `{x:real | &0 <= x /\ x < &1}`; `&0`; `x:real`]
                  HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
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
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + x) / (&1 - x) = exp(log(&1 + x) - log(&1 - x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG; REAL_ARITH `&0 <= x ==> &0 < &1 + x`;
                 REAL_SUB_LT];
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]);;

(* ------------------------------------------------------------------------- *)
(* x^(1/r) (x - 1) <= r x (x^(1/r) - 1) for x >= 0, r >= 1 and for x > 0,   *)
(* r < 0, the cases where t |-> t^(1 - 1/r) is concave or convex, resp.;     *)
(* and 2^(-x) <= 1 - x/2 for x in [0,1].                                     *)
(* ------------------------------------------------------------------------- *)

let RPOW_ROOT_SUB_LE = prove
 (`!x r. &0 <= x /\ &1 <= r \/ &0 < x /\ r < &0
         ==> x rpow (&1 / r) * (x - &1) <= r * x * (x rpow (&1 / r) - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ALL_TAC;
    MP_TAC(SPECL [`&1 - &1 / r`; `x:real`] RPOW_BERNOULLI_TANGENT) THEN
    ANTS_TAC THENL
     [DISJ1_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&1 <= &1 - a <=> &0 <= --a`] THEN
        REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_INV_NEG;
                    REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`x:real`; `&1`; `&1 / r`] RPOW_SUB) THEN
    ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`x:real`; `&1 / r`] RPOW_POS_LT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`x rpow (&1 / r)`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r * x <= r * ((&1 + (&1 - &1 / r) * (x - &1)) * y)`
    MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --r * (x - a) ==> r * x <= r * a`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(e:real) - d = b - a ==> a <= b ==> d <= e`) THEN
    UNDISCH_TAC `r < &0` THEN CONV_TAC REAL_FIELD] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_SIMP_TAC[RPOW_ZERO; REAL_DIV_EQ_0; REAL_LT_IMP_NZ; REAL_OF_NUM_EQ;
                 ARITH_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - &1 / r`; `x:real`] RPOW_BERNOULLI_TANGENT_REV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 <= &1 - a <=> a <= &1`;
                 REAL_ARITH `&1 - a <= &1 <=> &0 <= a`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `&1`; `&1 / r`] RPOW_SUB) THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`x:real`; `&1 / r`] RPOW_POS_LT) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`x rpow (&1 / r)`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r * x <= r * (&1 + (&1 - &1 / r) * (x - &1)) * y`
  MP_TAC THENL [ASM_SIMP_TAC[REAL_LE_LMUL_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(e:real) - d = b - a ==> a <= b ==> d <= e`) THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let RPOW_TWO_NEG_LE = prove
 (`!x. &0 <= x /\ x <= &1 ==> &2 rpow (--x) <= &1 - x / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_NEG; GSYM RPOW_INV] THEN
  MP_TAC(SPECL [`--(&1 / &2)`; `x:real`] RPOW_BERNOULLI_REV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* e^x <= 1 + x + x^2 for x <= c and e^(-x) <= 1 - x/2 for x in [0,c],      *)
(* whenever the inequality holds at c: each difference changes sign once on  *)
(* the relevant side. The constants c = 1.79 and c = 1.59 are checked by     *)
(* exact rational arithmetic: e^y <= (2 + y)/(2 - y) for y = 179/3200 and    *)
(* the cubic Taylor bound for y = 159/800, each raised to a power of 2.      *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_LOG_QUADRATIC_SUB = prove
 (`!y. ((\x. log(&1 + x + x pow 2) - x) has_real_derivative
        y * (&1 - y) / (&1 + y + y pow 2)) (atreal y)`,
  GEN_TAC THEN SUBGOAL_THEN `&0 < &1 + y + y pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `y + &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `&0 < &1 + y + y pow 2` THEN
  CONV_TAC REAL_FIELD);;

let REAL_EXP_179_100_LE = prove
 (`exp(&179 / &100) <= &1 + &179 / &100 + (&179 / &100) pow 2`,
  SUBGOAL_THEN `&179 / &100 = &32 * &2 * &179 / &6400`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_EXP_N] THEN
  TRANS_TAC REAL_LE_TRANS
   `((&1 + &179 / &6400) / (&1 - &179 / &6400)) pow 32` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_EXP_DOUBLE_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let LOG_QUADRATIC_GE = prove
 (`!c x. c <= log(&1 + c + c pow 2) /\ x <= c
         ==> x <= log(&1 + x + x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN `!y. &0 < &1 + y + y pow 2` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `y + &1 / &2` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x <= &1` THENL
   [MP_TAC(ISPECL [`\x. log(&1 + x + x pow 2) - x`;
                   `\y. y * (&1 - y) / (&1 + y + y pow 2)`;
                   `{x:real | x <= &1}`; `&0`; `x:real`]
                  REAL_DERIVATIVE_SIGN_MINIMUM) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
    SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN;
             HAS_REAL_DERIVATIVE_LOG_QUADRATIC_SUB] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[LOG_1; REAL_SUB_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= --y * z ==> y * z <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --(log(&1 + x + x pow 2) - x)`;
                 `\y. --(y * (&1 - y) / (&1 + y + y pow 2))`;
                 `{x:real | &1 <= x /\ x <= c}`; `x:real`; `c:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_LOG_QUADRATIC_SUB];
      REWRITE_TAC[REAL_NEG_GE0] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y * --z ==> y * z <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_EXP_QUADRATIC_UPPER_GEN = prove
 (`!c x. exp c <= &1 + c + c pow 2 /\ x <= c
         ==> exp x <= &1 + x + x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y. &0 < &1 + y + y pow 2` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `y + &1 / &2` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x <= log(&1 + x + x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC LOG_QUADRATIC_GE THEN EXISTS_TAC `c:real` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC RAND_CONV
     [GSYM(MATCH_MP EXP_LOG (SPEC `x:real` th))]) THEN
  ASM_REWRITE_TAC[REAL_EXP_MONO_LE]);;

let REAL_EXP_QUADRATIC_UPPER = prove
 (`!x. x <= &179 / &100 ==> exp x <= &1 + x + x pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EXP_QUADRATIC_UPPER_GEN THEN
  EXISTS_TAC `&179 / &100` THEN ASM_REWRITE_TAC[REAL_EXP_179_100_LE]);;

let REAL_EXP_159_100_GE = prove
 (`&200 / &41 <= exp(&159 / &100)`,
  SUBGOAL_THEN `&159 / &100 = &8 * &159 / &800` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_EXP_N] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&1 + &159 / &800 + (&159 / &800) pow 2 / &2 +
     (&159 / &800) pow 3 / &6) pow 8` THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_EXP_CUBIC_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let REAL_EXP_NEG_LE_LINEAR_GEN = prove
 (`!c x. exp(--c) <= &1 - c / &2 /\ &0 <= x /\ x <= c
         ==> exp(--x) <= &1 - x / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - c / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `--c:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&1 - c / &2) + c` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `--c <= l ==> &0 <= l + c`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y < &2 ==> ((\x. log(&1 - x / &2) + x) has_real_derivative
                    (&1 - y) / (&2 - y)) (atreal y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; UNDISCH_TAC `y < &2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&1 - x / &2) + x` MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN SUBGOAL_THEN `&0 < &1 - x / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG th)]) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `x <= &1` THENL
   [MP_TAC(ISPECL [`\x. log(&1 - x / &2) + x`; `\y. (&1 - y) / (&2 - y)`;
                   `{x:real | &0 <= x /\ x <= &1}`; `&0`; `x:real`]
                  HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[LOG_1; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --(log(&1 - x / &2) + x)`;
                 `\y. --((&1 - y) / (&2 - y))`;
                 `{x:real | &1 <= x /\ x <= c}`; `x:real`; `c:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_NEG_GE0; real_div] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_EXP_NEG_LE_LINEAR = prove
 (`!x. &0 <= x /\ x <= &159 / &100 ==> exp(--x) <= &1 - x / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EXP_NEG_LE_LINEAR_GEN THEN
  EXISTS_TAC `&159 / &100` THEN ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
  TRANS_TAC REAL_LE_TRANS `inv(&200 / &41)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_EXP_159_100_GE] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* x e^x >= x + x^2 + x^3/2, e^x <= x + e^(x^2) and e^x + e^(-x) <=          *)
(* 2 e^(x^2/2), for all real x. The last one rests on tanh x <= x, x >= 0.   *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_SUB_QUADRATIC_MONO = prove
 (`!a b. a <= b
         ==> exp a - (&1 + a + a pow 2 / &2) <=
             exp b - (&1 + b + b pow 2 / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. exp y - (&1 + y + y pow 2 / &2)`;
                 `\y. exp y - (&1 + y)`; `(:real)`; `a:real`; `b:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_UNIV; IS_REALINTERVAL_UNIV] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE; REAL_EXP_LE_X]];
    REWRITE_TAC[]]);;

let REAL_EXP_CUBIC_MUL_GE = prove
 (`!x. x + x pow 2 + x pow 3 / &2 <= x * exp x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  SUBGOAL_THEN `x * exp x - (x + x pow 2 + x pow 3 / &2) =
                x * (exp x - (&1 + x + x pow 2 / &2))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&0`; `x:real`] REAL_EXP_SUB_QUADRATIC_MONO) THEN
    ASM_REWRITE_TAC[REAL_EXP_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `(x:real) * y = --x * --y`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`x:real`; `&0`] REAL_EXP_SUB_QUADRATIC_MONO) THEN
      ASM_REWRITE_TAC[REAL_EXP_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC]]);;

let REAL_EXP_LE_ADD_EXP_SQUARE = prove
 (`!x. exp x <= x + exp(x pow 2)`,
  GEN_TAC THEN ASM_CASES_TAC `x <= &1` THENL
   [MP_TAC(SPEC `(x:real) pow 2` REAL_EXP_LE_X) THEN
    MP_TAC(SPEC `x:real` REAL_EXP_QUADRATIC_UPPER) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a <= b ==> a <= x + b`) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

let REAL_EXP_TANH_LE = prove
 (`!x. &0 <= x ==> exp x - exp(--x) <= x * (exp x + exp(--x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp(&2 * x) * (&1 - x) <= &1 + x` MP_TAC THENL
   [ASM_CASES_TAC `x < &1` THENL
     [MP_TAC(SPEC `x:real` REAL_EXP_DOUBLE_LE) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT];
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= e * (x - &1) /\ &0 <= x ==> e * (&1 - x) <= &1 + x`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * x) = exp x * exp x /\ exp(--x) * exp x = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_LINV; REAL_EXP_0] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `--x:real` REAL_EXP_POS_LE) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `exp(--x) * (exp x * exp x * (&1 - x)) <= exp(--x) * (&1 + x)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--x) * exp x * exp x * (&1 - x) = exp x * (&1 - x)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `exp(--x) * exp x = &1` THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

let REAL_COSH_LE_EXP_SQUARE = prove
 (`!x. exp x + exp(--x) <= &2 * exp(x pow 2 / &2)`,
  SUBGOAL_THEN
   `!x. &0 <= x ==> exp x + exp(--x) <= &2 * exp(x pow 2 / &2)`
  ASSUME_TAC THENL
   [ALL_TAC;
    GEN_TAC THEN DISJ_CASES_TAC(SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`) THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_POW_NEG; ARITH] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((exp x + exp(--x)) * exp(--(x pow 2 / &2)))`;
    `\y. exp(--(y pow 2 / &2)) * (y * (exp y + exp(--y)) -
                                  (exp y - exp(--y)))`;
    `{x:real | &0 <= x}`; `&0`; `x:real`]
   HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE; REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_EXP_TANH_LE]];
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_LE_NEG2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((exp x + exp(--x)) * exp(--(x pow 2 / &2))) * exp(x pow 2 / &2) <=
    &2 * exp(x pow 2 / &2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_LINV;
              REAL_EXP_0; REAL_MUL_RID]);;

let REAL_EXP_SQUARE_BOUNDS = prove
 (`!x. x + x pow 2 + x pow 3 / &2 <= x * exp x /\
       exp x <= x + exp(x pow 2) /\
       exp x + exp(--x) <= &2 * exp(x pow 2 / &2)`,
  REWRITE_TAC[REAL_EXP_CUBIC_MUL_GE; REAL_EXP_LE_ADD_EXP_SQUARE;
              REAL_COSH_LE_EXP_SQUARE]);;

(* ------------------------------------------------------------------------- *)
(* Comparing (1 + x/p)^p with (1 + x/q)^q. The map t |-> (1 + x/t)^t is      *)
(* increasing on t > 0 and on t < 0 wherever the base is positive, and the   *)
(* value at a positive t is at most e^x, which is at most the value at a     *)
(* negative t. This covers the five sign cases of the sheet together with    *)
(* their boundary cases.                                                     *)
(* ------------------------------------------------------------------------- *)

let RPOW_ADD_DIV_MONO = prove
 (`!x p q. &0 < q /\ q <= p /\ --q <= x
           ==> (&1 + x / q) rpow q <= (&1 + x / p) rpow p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--x:real`; `q:real`; `p:real`] REAL_EXP_LIMIT_RPOW_LE) THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; real_sub; REAL_NEG_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RPOW_ADD_DIV_MONO_NEG = prove
 (`!x p q. q <= p /\ p < &0 /\ x < --p
           ==> (&1 + x / q) rpow q <= (&1 + x / p) rpow p`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
  ONCE_REWRITE_TAC[RPOW_NEG] THEN
  SUBGOAL_THEN `!b. &1 + x / b = &1 - x / --b`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_NEG_GT0] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`x:real`; `--p:real`; `--q:real`]
                 REAL_EXP_LIMIT_RPOW_LE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RPOW_ADD_DIV_POS_LE_NEG = prove
 (`!x p q. q < &0 /\ &0 < p /\ --p <= x /\ x < --q
           ==> (&1 + x / p) rpow p <= (&1 + x / q) rpow q`,
  REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `exp x` THEN
  ASM_SIMP_TAC[RPOW_ADD_DIV_LE_EXP] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
  ONCE_REWRITE_TAC[RPOW_NEG] THEN
  SUBGOAL_THEN `!b. &1 + x / b = &1 - x / --b`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp x = inv(exp(--x))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ; REAL_NEG_GT0] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`--x:real`; `--q:real`] RPOW_ADD_DIV_LE_EXP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM real_sub]]);;
