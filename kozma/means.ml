(* ========================================================================= *)
(* Inequalities between means and related weighted products, from            *)
(* L. Kozma, "Useful Inequalities" (v0.44).                                  *)
(* ========================================================================= *)

needs "Library/permutations.ml";;
needs "Multivariate/realanalysis.ml";;
needs "kozma/finite_sums.ml";;
needs "kozma/log_trig_sqrt.ml";;

(* ------------------------------------------------------------------------- *)
(* The second part of Chong's inequality: for a_i >= 0 and a permutation p   *)
(* of the index set, prod a_i^a_(p i) <= prod a_i^a_i, with 0^0 = 1. If some *)
(* a_i = 0 has a_(p i) > 0 the left side is 0. Otherwise, in logarithms, it  *)
(* is sum a_(p i) ln a_i <= sum a_i ln a_i, from ln t <= t - 1 at            *)
(* t = a_i / a_(p i) after reindexing by p.                                  *)
(* ------------------------------------------------------------------------- *)

let SUM_MUL_LOG_PERMUTE_LE = prove
 (`!s (a:A->real) p.
     FINITE s /\ p permutes s /\
     (!i. i IN s ==> &0 <= a i /\ (a i = &0 ==> a(p i) = &0))
     ==> sum s (\i. a(p i) * log(a i)) <= sum s (\i. a i * log(a i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> &0 <= (a:A->real)((p:A->A) i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `sum s (\i. (a:A->real) i * log(a i)) =
     sum s (\i. a((p:A->A) i) * log(a(p i))) /\
     sum s a = sum s (\i. a(p i))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV[MATCH_MP SUM_PERMUTE
          th]) THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
    `sum s (\i. (a:A->real)((p:A->A) i) * log(a(p i)) + (a i - a(p i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN
    DISCH_TAC THEN BETA_TAC;
    ASM_SIMP_TAC[SUM_ADD; SUM_SUB] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
    `&0 <= (a:A->real) i /\ ((a:A->real) i = &0 ==> a((p:A->A) i) = &0) /\
     &0 <= a(p i)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(a:A->real) i = &0` THENL
   [SUBGOAL_THEN `(a:A->real)((p:A->A) i) = &0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[];
      ALL_TAC] THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_CASES_TAC `(a:A->real)((p:A->A) i) = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:A->real) i /\ &0 < a((p:A->A) i)`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `(a:A->real) i / a((p:A->A) i) - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (q - &1) = q`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; LOG_DIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `(a:A->real)((p:A->A) i) * (log(a i) - log(a(p i)))
     <= a(p i) * (a i / a(p i) - &1)`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A->real)((p:A->A) i) * (a i / a(p i) - &1) = a i - a(p i)`
    SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < (a:A->real)((p:A->A) i)` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC]);;

let PRODUCT_RPOW_PERMUTE_LE = prove
 (`!s (a:A->real) p.
     FINITE s /\ p permutes s /\ (!i. i IN s ==> &0 <= a i)
     ==> product s (\i. a i rpow a(p i)) <= product s (\i. a i rpow a i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> &0 <= (a:A->real)((p:A->A) i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  ASM_CASES_TAC
    `?i:A. i IN s /\ a i = &0 /\ ~((a:A->real)((p:A->A) i) = &0)` THENL
   [TRANS_TAC REAL_LE_TRANS `&0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `j:A` THEN ASM_REWRITE_TAC[RPOW_ZERO];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[RPOW_POS_LE]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM;
                              TAUT `~(a /\ b /\ ~c) <=> a /\ b ==> c`]) THEN
  SUBGOAL_THEN
    `!b:A->real. (!i. i IN s /\ a i = &0 ==> b i = &0)
                 ==> product s (\i. a i rpow b i) =
                     exp(sum s (\i. b i * log(a i)))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_EXP_SUM] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    BETA_TAC THEN REWRITE_TAC[rpow] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(a:A->real) i = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LE_LT];
      ALL_TAC] THEN ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_EXP_0];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `\i. (a:A->real)((p:A->A) i)` th) THEN
              MP_TAC(SPEC `a:A->real` th)) THEN BETA_TAC THEN ANTS_TAC THENL
   [SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC SUM_MUL_LOG_PERMUTE_LE THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The weighted AM-GM inequality for two terms: x^u y^v <= u x + v y for x,  *)
(* y, u, v >= 0 with u + v = 1.                                              *)
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

(* ------------------------------------------------------------------------- *)
(* Heinz: sqrt(x y) <= (x^(1-a) y^a + x^a y^(1-a)) / 2 <= (x + y) / 2 for a  *)
(* in [0,1], for all x, y >= 0.                                              *)
(* ------------------------------------------------------------------------- *)

let HEINZ_INEQUALITY = prove
 (`!x y a. &0 <= x /\ &0 <= y /\ &0 <= a /\ a <= &1
         ==> sqrt(x * y) <=
             (x rpow (&1 - a) * y rpow a + x rpow a * y rpow (&1 - a)) / &2 /\
             (x rpow (&1 - a) * y rpow a + x rpow a * y rpow (&1 - a)) / &2 <=
             (x + y) / &2`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN
      `x * y = (x rpow (&1 - a) * y rpow a) * (x rpow a * y rpow (&1 - a))`
      SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH
                         `(a * b) * (c * d) = (a * c) * (b * d):real`] THEN
      ASM_SIMP_TAC[GSYM RPOW_ADD_ALT; REAL_ARITH `(&1 - a) + (a:real) = &1`;
                   REAL_ARITH `(a:real) + (&1 - a) = &1`; RPOW_POW; REAL_POW_1;
                   REAL_ARITH `~(&1 = &0)`];
      ALL_TAC] THEN MATCH_MP_TAC AGM_SQRT THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LE_MUL];
    MP_TAC(SPECL[`x:real`; `y:real`; `&1 - (a:real)`; `a:real`]
             RPOW_MUL_RPOW_LE_WEIGHTED_SUM) THEN
    MP_TAC(SPECL[`x:real`; `y:real`; `a:real`; `&1 - (a:real)`]
             RPOW_MUL_RPOW_LE_WEIGHTED_SUM) THEN
    ASM_REWRITE_TAC[REAL_ARITH `(a:real) + (&1 - a) = &1`;
                    REAL_ARITH `(&1 - a) + (a:real) = &1`; REAL_SUB_LE] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The log mean (x - y) / (ln x - ln y). The chain of the sheet holds for x, *)
(* y > 0 with x <> y (at x = y the log mean is 0/0); its two outer links     *)
(* hold for all x, y >= 0. With c, d the fourth roots of x > y, the inner    *)
(* links reduce to 2 c d ln(c/d) <= c^2 - d^2 <= (c^2 + d^2) ln(c/d).        *)
(* ------------------------------------------------------------------------- *)

let LOG_DIV_SQUARE_BOUNDS = prove
 (`!c d. &0 < d /\ d < c
       ==> &2 * (c * d) * log(c / d) <= c pow 2 - d pow 2 /\
           c pow 2 - d pow 2 <= (c pow 2 + d pow 2) * log(c / d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < c /\ &1 < c / d` STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN CONJ_TAC THENL
   [SUBGOAL_THEN
      `(c:real) pow 2 - d pow 2 = &2 * (c * d) * ((c / d - inv(c / d)) / &2)`
      SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    (MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH `&0 <= &2`];
       ALL_TAC]) THEN MP_TAC(SPEC `c / d:real` LOG_ABS_LE_HALF_DIFF_INV) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    (MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
       ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < log(c / d:real) /\ inv(c / d:real) < &1`
       STRIP_ASSUME_TAC THENL
      [ASM_SIMP_TAC[LOG_POS_LT; REAL_INV_LT_1];
       ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `(c / d:real) pow 2 - &1` LOG_GE_DIV_HALF) THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 + ((x:real) - &1) = x`;
                REAL_ARITH `&2 + ((x:real) - &1) = x + &1`] THEN
    ASM_SIMP_TAC[LOG_POW; REAL_ARITH `&1 < x ==> &0 < x`] THEN
    (SUBGOAL_THEN `&0 < c pow 2 + d pow 2` ASSUME_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_ADD; REAL_POW_LT];
       ALL_TAC]) THEN
    (SUBGOAL_THEN
       `&2 * (((c:real) / d) pow 2 - &1) / ((c / d) pow 2 + &1) =
        &2 * (c pow 2 - d pow 2) / (c pow 2 + d pow 2)`
       SUBST1_TAC THENL
      [UNDISCH_TAC `&0 < c pow 2 + d pow 2` THEN UNDISCH_TAC `&0 < d` THEN
       CONV_TAC REAL_FIELD;
       ALL_TAC]) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                 REAL_ARITH `&2 * (x:real) / y = &2 * (x / y)`;
                 REAL_ARITH `&2 * x <= &2 * y <=> x <= y`] THEN
    REAL_ARITH_TAC]);;

let LOG_MEAN_POW4_BOUNDS = prove
 (`!c d. &0 < d /\ d < c
       ==> (c pow 2 + d pow 2) / &2 * (c * d) <=
           (c pow 4 - d pow 4) / (log(c pow 4) - log(d pow 4)) /\
           (c pow 4 - d pow 4) / (log(c pow 4) - log(d pow 4)) <=
           ((c pow 2 + d pow 2) / &2) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `log(c pow 4) - log(d pow 4) = &4 * log(c / d)`
     SUBST1_TAC THENL
    [ASM_SIMP_TAC[LOG_POW; LOG_DIV] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  MP_TAC(SPECL[`c:real`; `d:real`] LOG_DIV_SQUARE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < log(c / d)` ASSUME_TAC THENL
    [MATCH_MP_TAC LOG_POS_LT THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < c pow 2 + d pow 2` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_LT_ADD; REAL_POW_LT];
     ALL_TAC]) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL;
               REAL_ARITH `&0 < &4`] THEN
  (CONJ_TAC THENL
    [MP_TAC(ISPECL[`(c:real) pow 2 + (d:real) pow 2`;
                   `&2 * ((c:real) * d) * log(c / d)`;
                   `(c:real) pow 2 - (d:real) pow 2`] REAL_LE_LMUL);
     MP_TAC(ISPECL[`(c:real) pow 2 + (d:real) pow 2`;
                   `(c:real) pow 2 - (d:real) pow 2`;
                   `((c:real) pow 2 + (d:real) pow 2) * log(c / d)`]
              REAL_LE_LMUL)] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
   REAL_ARITH_TAC));;

let LOG_MEAN_OUTER_BOUNDS = prove
 (`!x y. &0 <= x /\ &0 <= y
       ==> sqrt(x * y) <= (sqrt x + sqrt y) / &2 * (x * y) rpow (&1 / &4) /\
           ((sqrt x + sqrt y) / &2) pow 2 <= (x + y) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(x * y) rpow (&1 / &4) = sqrt(sqrt x * sqrt y)`
     SUBST1_TAC THENL
    [ASM_SIMP_TAC[GSYM SQRT_MUL; GSYM RPOW_SQRT; REAL_LE_MUL; RPOW_POS_LE;
                  RPOW_RPOW] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `!a b. &0 <= a /\ &0 <= b
            ==> a * b <= (a + b) / &2 * sqrt(a * b) /\
                ((a + b) / &2) pow 2 <= (a pow 2 + b pow 2) / &2`
     (MP_TAC o SPECL[`sqrt x`; `sqrt y`]) THENL
    [REPEAT STRIP_TAC THENL
      [MP_TAC(SPECL[`a:real`; `b:real`] AGM_SQRT) THEN ASM_REWRITE_TAC[] THEN
       DISCH_TAC THEN
       SUBGOAL_THEN `a * b = sqrt(a * b) * sqrt(a * b)`
         (fun th -> GEN_REWRITE_TAC LAND_CONV[th]) THENL
        [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LE_MUL];
         MATCH_MP_TAC REAL_LE_RMUL THEN
         ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL]];
       REWRITE_TAC[REAL_ARITH
                     `((a + b) / &2) pow 2 <= (a pow 2 + b pow 2) / &2 <=>
                      &0 <= (a - b) pow 2`;
                   REAL_LE_POW_2]];
     ALL_TAC]) THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; SQRT_MUL]);;

let LOG_MEAN_INEQUALITY = prove
 (`!x y. &0 < x /\ &0 < y /\ ~(x = y)
       ==> sqrt(x * y) <= (sqrt x + sqrt y) / &2 * (x * y) rpow (&1 / &4) /\
           (sqrt x + sqrt y) / &2 * (x * y) rpow (&1 / &4)
           <= (x - y) / (log x - log y) /\
           (x - y) / (log x - log y) <= ((sqrt x + sqrt y) / &2) pow 2 /\
           ((sqrt x + sqrt y) / &2) pow 2 <= (x + y) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`x:real`; `y:real`] LOG_MEAN_OUTER_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `?c d. &0 < c /\ &0 < d /\ x = c pow 4 /\ y = d pow 4`
     STRIP_ASSUME_TAC THENL
    [MAP_EVERY EXISTS_TAC[`sqrt(sqrt x)`; `sqrt(sqrt y)`] THEN
     ASM_SIMP_TAC[SQRT_POS_LT; ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW;
                  SQRT_POW_2; SQRT_POS_LE; REAL_LT_IMP_LE];
     ALL_TAC]) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  (SUBGOAL_THEN
     `sqrt(c pow 4) = c pow 2 /\ sqrt(d pow 4) = d pow 2 /\
      (c pow 4 * d pow 4) rpow (&1 / &4) = c * d`
     (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
     ASM_SIMP_TAC[POW_2_SQRT; REAL_POW_LE; REAL_LT_IMP_LE] THEN
     REWRITE_TAC[REAL_POW_POW; ARITH_RULE `2 * 2 = 4`; GSYM REAL_POW_MUL;
                 GSYM RPOW_POW] THEN
     ASM_SIMP_TAC[RPOW_RPOW; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_POW; REAL_POW_1];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `d < (c:real)` THENL
    [ASM_SIMP_TAC[LOG_MEAN_POW4_BOUNDS];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `c < (d:real)` ASSUME_TAC THENL
    [ASM_MESON_TAC[REAL_LT_TOTAL];
     ALL_TAC]) THEN MP_TAC(SPECL[`d:real`; `c:real`] LOG_MEAN_POW4_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN
     `(d pow 4 - c pow 4) / (log(d pow 4) - log(c pow 4)) =
      (c pow 4 - d pow 4) / (log(c pow 4) - log(d pow 4))`
     SUBST1_TAC THENL
    [GEN_REWRITE_TAC(LAND_CONV o BINOP_CONV) [GSYM REAL_NEG_SUB] THEN
     REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG;
                 REAL_NEG_NEG];
     ALL_TAC]) THEN REWRITE_TAC[REAL_ADD_SYM; REAL_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Young: (1/(p x^p) + 1/(q y^q))^-1 <= x y <= x^p/p + y^q/q for x, y, p, q  *)
(* > 0 with 1/p + 1/q = 1. The upper bound is the library's                  *)
(* YOUNG_INEQUALITY, the lower bound is the same inequality at 1/x, 1/y.     *)
(* ------------------------------------------------------------------------- *)

let YOUNG_INEQUALITY_BOUNDS = prove
 (`!x y p q. &0 < x /\ &0 < y /\ &0 < p /\ &0 < q /\ inv p + inv q = &1
           ==> inv(&1 / (p * x rpow p) + &1 / (q * y rpow q)) <= x * y /\
               x * y <= x rpow p / p + y rpow q / q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC YOUNG_INEQUALITY THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]) THEN
  MP_TAC(SPECL[`inv x:real`; `inv y:real`; `p:real`; `q:real`]
           YOUNG_INEQUALITY) THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; RPOW_INV] THEN DISCH_TAC THEN
  (SUBGOAL_THEN
     `&1 / (p * x rpow p) + &1 / (q * y rpow q) =
      inv(x rpow p) / p + inv(y rpow q) / q`
     SUBST1_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_MUL] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN GEN_REWRITE_TAC RAND_CONV[GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_INV_MUL; REAL_LT_MUL; REAL_LT_INV_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Mahler: prod (x_i + y_i)^(1/n) >= prod x_i^(1/n) + prod y_i^(1/n) for     *)
(* x_i, y_i >= 0 over a nonempty finite index set of size n; the case of     *)
(* equal weights of the library's HOELDER.                                   *)
(* ------------------------------------------------------------------------- *)

let MAHLER_INEQUALITY = prove
 (`!s:A->bool x y.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 <= x i /\ &0 <= y i)
     ==> product s (\i. x i rpow (&1 / &(CARD s))) +
         product s (\i. y i rpow (&1 / &(CARD s))) <=
         product s (\i. (x i + y i) rpow (&1 / &(CARD s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`s:A->bool`; `\i:A. &1 / &(CARD(s:A->bool))`; `x:A->real`;
                `y:A->real`] HOELDER) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_LE_DIV; REAL_POS] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_EQ; CARD_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Weierstrass. prod (1 + d_i) >= 1 + sum d_i when the d_i are all >= 0 or   *)
(* all in [-1,0]. With Bernoulli's inequality this gives 1 - sum w_i x_i <=  *)
(* prod (1 - x_i)^w_i for x_i in [0,1] and 1 + sum w_i x_i <= prod (1 +      *)
(* x_i)^w_i for x_i >= 0, both for w_i >= 1. The upper bounds hold for all   *)
(* w_i >= 0: prod (1 + x_i)^w_i <= prod (1 - x_i)^(-w_i) for x_i in [-1,1),  *)
(* and, from (1 + x)^w <= exp(w x), prod (1 + x_i)^w_i <= (1 - sum w_i       *)
(* x_i)^-1 for x_i >= -1 with sum w_i x_i < 1, and prod (1 - x_i)^w_i <= (1  *)
(* + sum w_i x_i)^-1 for x_i <= 1 with sum w_i x_i > -1.                     *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ONE_ADD_GE = prove
 (`!s:A->bool d.
     FINITE s /\
     ((!i. i IN s ==> &0 <= d i) \/ (!i. i IN s ==> -- &1 <= d i /\ d i <= &0))
     ==> &1 + sum s d <= product s (\i. &1 + d i)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:A->bool`, `s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES; REAL_LE_REFL; REAL_ADD_RID] THEN
  MAP_EVERY X_GEN_TAC[`a:A`; `t:A->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN DISCH_TAC THEN
  (FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ANTS_TAC THENL
    [ASM_MESON_TAC[];
     DISCH_TAC]) THEN
  (SUBGOAL_THEN `&0 <= (d:A->real) a * sum t d /\ &0 <= &1 + d a`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM DISJ_CASES_TAC THENL
      [ASM_SIMP_TAC[REAL_LE_MUL; SUM_POS_LE] THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     MP_TAC(ISPECL[`d:A->real`; `\i:A. &0`; `t:A->bool`] SUM_LE) THEN
     ASM_SIMP_TAC[SUM_0] THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL;
       ALL_TAC] THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN ASM_SIMP_TAC[SUM_CLAUSES; PRODUCT_CLAUSES] THEN
  (TRANS_TAC REAL_LE_TRANS `(&1 + (d:A->real) a) * (&1 + sum t d)` THEN
   CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]));;

let PRODUCT_RPOW_ONE_SUB_GE = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ x i <= &1 /\ &1 <= w i)
     ==> &1 - sum s (\i. w i * x i) <= product s (\i. (&1 - x i) rpow w i)`,
  REPEAT STRIP_TAC THEN
  (MP_TAC(ISPECL[`s:A->bool`; `\i:A. (&1 - x i) rpow w i - &1`]
            PRODUCT_ONE_ADD_GE) THEN
   REWRITE_TAC[REAL_ARITH `&1 + ((a:real) - &1) = a`] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN MP_TAC(ISPECL[`w(i:A):real`; `&1 - x(i:A)`] RPOW_1_LE) THEN
     MP_TAC(ISPECL[`&1 - x(i:A)`; `w(i:A):real`] RPOW_POS_LE) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `--a <= b ==> &1 + b <= c ==> &1 - a <= c`) THEN
  ASM_SIMP_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (MP_TAC(ISPECL[`--(x(i:A)):real`; `w(i:A):real`] RPOW_BERNOULLI) THEN
   REWRITE_TAC[GSYM real_sub] THEN ANTS_TAC THENL
    [ASM_REAL_ARITH_TAC;
     REAL_ARITH_TAC]));;

let PRODUCT_RPOW_ONE_ADD_GE = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ &1 <= w i)
     ==> &1 + sum s (\i. w i * x i) <= product s (\i. (&1 + x i) rpow w i)`,
  REPEAT STRIP_TAC THEN
  (MP_TAC(ISPECL[`s:A->bool`; `\i:A. (&1 + x i) rpow w i - &1`]
            PRODUCT_ONE_ADD_GE) THEN
   REWRITE_TAC[REAL_ARITH `&1 + ((a:real) - &1) = a`] THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN MP_TAC(ISPECL[`&1 + x(i:A)`; `w(i:A):real`] RPOW_LE_1) THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
     ALL_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + b <= c ==> &1 + a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (MP_TAC(ISPECL[`x(i:A):real`; `w(i:A):real`] RPOW_BERNOULLI) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]));;

let PRODUCT_RPOW_ONE_ADD_LE_ONE_SUB = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> -- &1 <= x i /\ x i < &1 /\ &0 <= w i)
     ==> product s (\i. (&1 + x i) rpow w i) <=
         product s (\i. (&1 - x i) rpow --(w i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < (&1 - x(i:A)) rpow w i` ASSUME_TAC THENL
    [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN REWRITE_TAC[RPOW_NEG] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_MUL_LID; GSYM RPOW_MUL] THEN
  (MATCH_MP_TAC RPOW_1_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_ARITH `(&1 + (x:real)) * (&1 - x) = &1 - x * x`] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &1 - y <= &1`) THEN
     REWRITE_TAC[REAL_LE_SQUARE]]));;

let PRODUCT_RPOW_ONE_ADD_LE_INV = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> -- &1 <= x i /\ &0 <= w i) /\
     sum s (\i. w i * x i) < &1
     ==> product s (\i. (&1 + x i) rpow w i)
         <= inv(&1 - sum s (\i. w i * x i))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `exp(sum s (\i:A. w i * x i))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    (ASM_CASES_TAC `w(i:A) = &0` THENL
      [ASM_REWRITE_TAC[RPOW_0; REAL_MUL_LZERO; REAL_EXP_0; REAL_LE_REFL];
       ALL_TAC]) THEN
    (MP_TAC(ISPECL[`(w:A->real) i * (x:A->real) i`; `(w:A->real) i`]
              RPOW_ADD_DIV_LE_EXP) THEN ANTS_TAC THENL
      [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[REAL_ARITH `--w <= w * x <=> &0 <= w * (x + &1)`] THEN
       MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    (SUBGOAL_THEN `((w:A->real) i * (x:A->real) i) / w i = x i`
       SUBST1_TAC THENL
      [UNDISCH_TAC `~((w:A->real) i = &0)` THEN CONV_TAC REAL_FIELD;
       REWRITE_TAC[]]);
    SUBGOAL_THEN
      `&0 < exp(--sum s (\i:A. w i * x i)) /\
       &1 - sum s (\i:A. w i * x i) <= exp(--sum s (\i:A. w i * x i))`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MP_TAC(SPEC `--sum s (\i:A. w i * x i)` REAL_EXP_LE_X) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN REWRITE_TAC[REAL_EXP_NEG] THEN
    GEN_REWRITE_TAC LAND_CONV[GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[GSYM REAL_EXP_NEG] THEN
    ASM_REAL_ARITH_TAC]);;

let PRODUCT_RPOW_ONE_SUB_LE_INV = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> x i <= &1 /\ &0 <= w i) /\
     -- &1 < sum s (\i. w i * x i)
     ==> product s (\i. (&1 - x i) rpow w i)
         <= inv(&1 + sum s (\i. w i * x i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. --((x:A->real) i)`]
           PRODUCT_RPOW_ONE_ADD_LE_INV) THEN
  ASM_SIMP_TAC[GSYM real_sub; REAL_MUL_RNEG; SUM_NEG; REAL_SUB_RNEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `x <= &1 ==> -- &1 <= --x`];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The mediant inequality: min a_i/b_i <= sum a / sum b <= max a_i/b_i for   *)
(* b_i > 0. The second line of the means is its case a_i = |x_i|, b_i =      *)
(* |y_i| with y_i <> 0.                                                      *)
(* ------------------------------------------------------------------------- *)

let SUM_DIV_SUM_BOUNDS = prove
 (`!s:A->bool a b.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 < b i)
     ==> inf {a i / b i | i IN s} <= sum s a / sum s b /\
         sum s a / sum s b <= sup {a i / b i | i IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sum s (b:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LT_ALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{(a:A->real) i / b i | i IN s}` INF_FINITE) THEN
  MP_TAC(ISPEC `{(a:A->real) i / b i | i IN s}` SUP_FINITE) THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:A`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ];
    ASM_SIMP_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:A`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ]]);;

let SUM_ABS_RATIO_BOUNDS = prove
 (`!s:A->bool x y.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> ~(y i = &0))
     ==> inf {abs(x i) / abs(y i) | i IN s} <=
         sum s (\i. abs(x i)) / sum s (\i. abs(y i)) /\
         sum s (\i. abs(x i)) / sum s (\i. abs(y i)) <=
         sup {abs(x i) / abs(y i) | i IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`s:A->bool`; `\i:A. abs((x:A->real) i)`;
                `\i:A. abs((y:A->real) i)`] SUM_DIV_SUM_BOUNDS) THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ]);;

(* ------------------------------------------------------------------------- *)
(* The chain min <= HM <= GM <= AM <= QM <= sum x^2 / sum x <= max over a    *)
(* nonempty finite index set of size n, for x_i > 0; min and max are the inf *)
(* and sup of the finite set of values. The links from GM on hold for x_i >= *)
(* 0, AM <= QM for all real x_i, and QM <= sum x^2 / sum x whenever sum x >  *)
(* 0.                                                                        *)
(* ------------------------------------------------------------------------- *)

let SUM_POW_2_LE_CARD_MUL = prove
 (`!s:A->bool x.
     FINITE s ==> sum s x pow 2 <= &(CARD s) * sum s (\i. x i pow 2)`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `s:A->bool = {}` THENL
    [ASM_REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < &(CARD(s:A->bool))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ; CARD_EQ_0];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `!c. &0
          <= sum s (\i:A. (x:A->real) i pow 2) - &2 * c * sum s x +
             &(CARD(s:A->bool)) * c pow 2`
     (MP_TAC o SPEC `sum s (x:A->real) / &(CARD(s:A->bool))`) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `&0 <= sum s (\i:A. ((x:A->real) i - c) pow 2)` MP_TAC THENL
      [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
       ALL_TAC] THEN
     REWRITE_TAC[REAL_ARITH
                   `(a - c:real) pow 2 =
                    (a pow 2 - &2 * c * a) + c pow 2`] THEN
     ASM_SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; SUM_CONST; ETA_AX] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[REAL_FIELD
                 `&0 < n
                  ==> q - &2 * (s / n) * s + n * (s / n) pow 2 =
                      (n * q - s pow 2) / n`;
               REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let MEAN_LE_QUADRATIC_MEAN = prove
 (`!s:A->bool x. FINITE s
     ==> sum s x / &(CARD s) <= sqrt(sum s (\i. x i pow 2) / &(CARD s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  (ASM_CASES_TAC `CARD(s:A->bool) = 0` THENL
    [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < &(CARD(s:A->bool))` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`; `x:A->real`] SUM_POW_2_LE_CARD_MUL) THEN
  ASM_REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
               REAL_POW_LT] THEN DISCH_TAC THEN
  (SUBGOAL_THEN
     `sum s (\i:A. (x:A->real) i pow 2) / &(CARD(s:A->bool)) *
      &(CARD s) pow 2 =
      &(CARD s) * sum s (\i. x i pow 2)`
     SUBST1_TAC THENL
    [UNDISCH_TAC `&0 < &(CARD(s:A->bool))` THEN CONV_TAC REAL_FIELD;
     ASM_REWRITE_TAC[]]));;

let QUADRATIC_MEAN_LE_CONTRAHARMONIC_MEAN = prove
 (`!s:A->bool x. FINITE s /\ &0 < sum s x
     ==> sqrt(sum s (\i. x i pow 2) / &(CARD s))
         <= sum s (\i. x i pow 2) / sum s x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  (SUBGOAL_THEN `~(CARD(s:A->bool) = 0)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `&0 < sum {} (x:A->real)` THEN
     REWRITE_TAC[SUM_CLAUSES; REAL_LT_REFL];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `&0 < &(CARD(s:A->bool)) /\ &0 <= sum s (\i:A. (x:A->real) i pow 2)`
     STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ] THEN MATCH_MP_TAC SUM_POS_LE THEN
     REWRITE_TAC[REAL_LE_POW_2];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`; `x:A->real`] SUM_POW_2_LE_CARD_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POW_DIV; REAL_LE_LDIV_EQ;
               REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  (SUBGOAL_THEN `&0 < sum s (x:A->real) pow 2` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_POW_LT];
     ALL_TAC]) THEN REWRITE_TAC[REAL_FIELD `a / b * c = (c * a) / b:real`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(ISPECL[`sum s (\i:A. (x:A->real) i pow 2)`; `sum s (x:A->real) pow 2`;
                `&(CARD(s:A->bool)) * sum s (\i:A. (x:A->real) i pow 2)`]
           REAL_LE_LMUL) THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
  REAL_ARITH_TAC);;

let MEANS_INEQUALITY_POS_LE = prove
 (`!s:A->bool x.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 <= x i)
     ==> product s x rpow (&1 / &(CARD s)) <= sum s x / &(CARD s) /\
         sum s x / &(CARD s) <= sqrt(sum s (\i. x i pow 2) / &(CARD s)) /\
         sqrt(sum s (\i. x i pow 2) / &(CARD s))
         <= sum s (\i. x i pow 2) / sum s x /\
         sum s (\i. x i pow 2) / sum s x <= sup {x i | i IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MEAN_LE_QUADRATIC_MEAN] THEN
  (SUBGOAL_THEN `~(CARD(s:A->bool) = 0)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[CARD_EQ_0];
     ALL_TAC]) THEN
  (CONJ_TAC THENL
    [ASM_SIMP_TAC[RPOW_PRODUCT] THEN
     MP_TAC(ISPECL[`s:A->bool`; `x:A->real`; `CARD(s:A->bool)`] AGM_RPOW) THEN
     ASM_SIMP_TAC[HAS_SIZE; real_div; SUM_RMUL];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 <= sum s (x:A->real)` MP_TAC THENL
    [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [MP_TAC(ISPEC `{(x:A->real) i | i IN s}` SUP_FINITE) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[QUADRATIC_MEAN_LE_CONTRAHARMONIC_MEAN; REAL_LE_LDIV_EQ] THEN
    ASM_SIMP_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(ASSUME_TAC o SYM) THEN
    (SUBGOAL_THEN `!i:A. i IN s ==> (x:A->real) i = &0` ASSUME_TAC THENL
      [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[];
       ALL_TAC]) THEN
    (SUBGOAL_THEN `sum s (\i:A. (x:A->real) i pow 2) = &0` SUBST1_TAC THENL
      [MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[REAL_POW_ZERO; ARITH_EQ];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; SQRT_0; REAL_LE_REFL] THEN
    MP_TAC(ISPEC `{(x:A->real) i | i IN s}` SUP_FINITE) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; IN_IMAGE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL]]);;

let MEANS_INEQUALITY = prove
 (`!s:A->bool x.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 < x i)
     ==> inf {x i | i IN s} <= &(CARD s) / sum s (\i. inv(x i)) /\
         &(CARD s) / sum s (\i. inv(x i))
         <= product s x rpow (&1 / &(CARD s)) /\
         product s x rpow (&1 / &(CARD s)) <= sum s x / &(CARD s) /\
         sum s x / &(CARD s) <= sqrt(sum s (\i. x i pow 2) / &(CARD s)) /\
         sqrt(sum s (\i. x i pow 2) / &(CARD s))
         <= sum s (\i. x i pow 2) / sum s x /\
         sum s (\i. x i pow 2) / sum s x <= sup {x i | i IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`s:A->bool`; `x:A->real`] MEANS_INEQUALITY_POS_LE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN
     `~(CARD(s:A->bool) = 0) /\ &0 < sum s (\i:A. inv((x:A->real) i))`
     STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[CARD_EQ_0] THEN MATCH_MP_TAC SUM_POS_LT_ALL THEN
     ASM_SIMP_TAC[REAL_LT_INV_EQ];
     ALL_TAC]) THEN
  (CONJ_TAC THENL
    [MP_TAC(ISPECL[`s:A->bool`; `\i:A. &1`; `\i:A. inv((x:A->real) i)`]
              SUM_DIV_SUM_BOUNDS) THEN
     ASM_SIMP_TAC[REAL_LT_INV_EQ; SUM_CONST; REAL_MUL_RID; real_div;
                  REAL_MUL_LID; REAL_INV_INV] THEN SIMP_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`; `\i:A. inv((x:A->real) i)`; `CARD(s:A->bool)`]
           AGM_RPOW) THEN
  ASM_SIMP_TAC[HAS_SIZE; REAL_LE_INV_EQ; REAL_LT_IMP_LE; RPOW_INV; PRODUCT_INV;
               real_div; SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM RPOW_PRODUCT; GSYM real_div] THEN DISCH_TAC THEN
  (SUBGOAL_THEN
     `&0 < product s (x:A->real) rpow (&1 / &(CARD(s:A->bool))) /\
      &0 < &(CARD(s:A->bool))`
     STRIP_ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ] THEN MATCH_MP_TAC RPOW_POS_LT THEN
     MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC
    `inv(product s (x:A->real) rpow (&1 / &(CARD(s:A->bool))))
     <= sum s (\i:A. inv(x i)) / &(CARD s)` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`product s (x:A->real) rpow (&1 / &(CARD(s:A->bool)))`;
                `inv(product s (x:A->real) rpow (&1 / &(CARD(s:A->bool)))) *
                 &(CARD(s:A->bool))`;
                `sum s (\i:A. inv((x:A->real) i))`] REAL_LE_LMUL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               REAL_MUL_LID] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Ky Fan: prod x_i^a_i / prod (1 - x_i)^a_i <= sum a_i x_i / sum a_i (1 -   *)
(* x_i) for x_i in [0,1/2] and a_i >= 0 with sum a_i = 1 (so a_i <= 1),      *)
(* where 0^0 = 1. It is Jensen's inequality for the convex function ln((1 -  *)
(* t)/t) on (0,1/2].                                                         *)
(* ------------------------------------------------------------------------- *)

let REAL_CONVEX_ON_LOG_ONE_SUB_SUB_LOG = prove
 (`(\t. log(&1 - t) - log t) real_convex_on {t | &0 < t /\ t <= &1 / &2}`,
  MP_TAC(ISPECL[`\t. log(&1 - t) - log t`; `\t:real. --inv(&1 - t) - inv t`;
                `{t | &0 < t /\ t <= &1 / &2}`]
           REAL_CONVEX_ON_DERIVATIVE_INCREASING) THEN
  (ANTS_TAC THENL
    [CONJ_TAC THENL
      [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
       ALL_TAC] THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
     ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < &1 - x /\ &0 < &1 - y` STRIP_ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `(--inv(&1 - y) - inv y) - (--inv(&1 - x) - inv (x:real)) =
      (y - x) * (&1 - x - y) / (x * y * (&1 - x) * (&1 - y))`
     MP_TAC THENL
    [MAP_EVERY UNDISCH_TAC[`&0 < x`; `&0 < y`; `&0 < &1 - x`;
                           `&0 < &1 - y`] THEN CONV_TAC REAL_FIELD;
     ALL_TAC]) THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  ASM_REWRITE_TAC[] THEN
  (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC;
       REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
       ASM_REAL_ARITH_TAC]]));;

let KY_FAN_INEQUALITY_POS = prove
 (`!k:A->bool a x.
     FINITE k /\ (!i. i IN k ==> &0 < x i /\ x i <= &1 / &2 /\ &0 <= a i) /\
     sum k a = &1
     ==> product k (\i. x i rpow a i) / product k (\i. (&1 - x i) rpow a i) <=
         sum k (\i. a i * x i) / sum k (\i. a i * (&1 - x i))`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `sum k (\i:A. a i * (&1 - x i)) = &1 - sum k (\i. a i * x i)`
     SUBST1_TAC THENL
    [ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; SUM_SUB; ETA_AX];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `sum k (\i:A. a i * x i) <= &1 / &2` ASSUME_TAC THENL
    [TRANS_TAC REAL_LE_TRANS `sum k (\i:A. a i * &1 / &2)` THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[REAL_LE_LMUL];
       ASM_SIMP_TAC[SUM_RMUL; REAL_MUL_LID; real_div; ETA_AX] THEN
       REAL_ARITH_TAC];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < sum k (\i:A. a i * x i)` ASSUME_TAC THENL
    [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
      [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
       ALL_TAC] THEN DISCH_THEN(MP_TAC o SYM) THEN DISCH_TAC THEN
     MP_TAC(ISPECL[`\i:A. a i * (x:A->real) i`; `k:A->bool`] SUM_POS_EQ_0) THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ENTIRE;
                  REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
     UNDISCH_TAC `sum k (a:A->real) = &1` THEN ASM_SIMP_TAC[SUM_EQ_0] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `product k (\i:A. x i rpow a i) = exp(sum k (\i. a i * log(x i))) /\
      product k (\i:A. (&1 - x i) rpow a i) =
      exp(sum k (\i. a i * log(&1 - x i)))`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
    [ASM_SIMP_TAC[REAL_EXP_SUM] THEN CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
     X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN REWRITE_TAC[rpow] THEN COND_CASES_TAC THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `sum k (\i:A. a i * x i) / (&1 - sum k (\i. a i * x i)) =
      exp(log(sum k (\i:A. a i * x i)) - log(&1 - sum k (\i. a i * x i)))`
     SUBST1_TAC THENL
    [REWRITE_TAC[REAL_EXP_SUB] THEN BINOP_TAC THEN CONV_TAC SYM_CONV THEN
     MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN REWRITE_TAC[GSYM REAL_EXP_SUB; REAL_EXP_MONO_LE] THEN
  (MP_TAC(ISPECL[`\t. log(&1 - t) - log t`; `{t | &0 < t /\ t <= &1 / &2}`;
                 `k:A->bool`; `a:A->real`; `x:A->real`]
            REAL_CONVEX_ON_IMP_JENSEN) THEN
   ASM_SIMP_TAC[REAL_CONVEX_ON_LOG_ONE_SUB_SUB_LOG; IN_ELIM_THM] THEN
   ANTS_TAC THENL
    [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `sum k (\i:A. a i * (log(&1 - x i) - log(x i))) =
      sum k (\i. a i * log(&1 - x i)) - sum k (\i. a i * log(x i))`
     (fun th -> REWRITE_TAC[th]) THENL
    [ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB];
     DISCH_THEN(ACCEPT_TAC o MATCH_MP(REAL_ARITH
           `!a b c d:real. a - b <= c - d ==> d - c <= b - a`))]));;

let KY_FAN_INEQUALITY = prove
 (`!s:A->bool a x.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ x i <= &1 / &2 /\ &0 <= a i) /\
     sum s a = &1
     ==> product s (\i. x i rpow a i) / product s (\i. (&1 - x i) rpow a i) <=
         sum s (\i. a i * x i) / sum s (\i. a i * (&1 - x i))`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `?i:A. i IN s /\ x i = &0 /\ ~(a i = &0)` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `product s (\i:A. x i rpow a i) = &0` SUBST1_TAC THENL
      [ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `j:A` THEN
       ASM_REWRITE_TAC[RPOW_ZERO];
       ALL_TAC] THEN REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
     REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_DIV THEN
     CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[] THEN
     X_GEN_TAC `k:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:A`) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM;
                              TAUT `~(a /\ b /\ ~c) <=> a /\ b ==> c`]) THEN
  MP_TAC(ISPECL[`{i:A | i IN s /\ ~(a i = &0)}`; `a:A->real`; `x:A->real`]
           KY_FAN_INEQUALITY_POS) THEN
  (SUBGOAL_THEN `{i:A | i IN s /\ ~(a i = &0)} SUBSET s` ASSUME_TAC THENL
    [SET_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `(!f. (!i:A. i IN s /\ a i = &0 ==> f i = &1)
           ==> product {i | i IN s /\ ~(a i = &0)} f = product s f) /\
      (!g. (!i:A. i IN s /\ a i = &0 ==> g i = &0)
           ==> sum {i | i IN s /\ ~(a i = &0)} g = sum s g)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THENL
      [MATCH_MP_TAC PRODUCT_SUPERSET;
       MATCH_MP_TAC SUM_SUPERSET] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
     ALL_TAC]) THEN ASM_SIMP_TAC[RPOW_0; REAL_MUL_LZERO; FINITE_RESTRICT] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:A` THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Radon: sum x_i^p / a_i^(p-1) >= (sum x)^p / (sum a)^(p-1) for p >= 1 and  *)
(* x_i, a_i >= 0, assuming for p > 1 that x_i = 0 wherever a_i = 0 (the term *)
(* is undefined otherwise); the reverse inequality for p in [0,1] needs      *)
(* nothing more. Both directions follow from sum x_i^p a_i^(1-p) <= (sum     *)
(* x)^p (sum a)^(1-p) for p in [0,1].                                        *)
(* ------------------------------------------------------------------------- *)

let SUM_RPOW_MUL_RPOW_LE = prove
 (`!s:A->bool x a p.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ &0 <= a i) /\ &0 <= p /\ p <= &1
     ==> sum s (\i. x i rpow p * a i rpow (&1 - p)) <=
         sum s x rpow p * sum s a rpow (&1 - p)`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `&0 <= sum s (x:A->real) /\ &0 <= sum s (a:A->real)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `sum s (x:A->real) = &0` THENL
    [SUBGOAL_THEN `!i:A. i IN s ==> x i = &0` ASSUME_TAC THENL
      [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[];
       ALL_TAC] THEN ASM_CASES_TAC `p = &0` THENL
      [ASM_SIMP_TAC[RPOW_0; REAL_SUB_RZERO; RPOW_POW; REAL_POW_1; REAL_MUL_LID;
                    ETA_AX; REAL_LE_REFL];
       ALL_TAC] THEN
     ASM_SIMP_TAC[RPOW_ZERO; REAL_MUL_LZERO; SUM_0; REAL_LE_REFL];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `sum s (a:A->real) = &0` THENL
    [SUBGOAL_THEN `!i:A. i IN s ==> a i = &0` ASSUME_TAC THENL
      [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[];
       ALL_TAC] THEN ASM_CASES_TAC `p = &1` THENL
      [ASM_SIMP_TAC[REAL_SUB_REFL; RPOW_0; RPOW_POW; REAL_POW_1; REAL_MUL_RID;
                    ETA_AX; REAL_LE_REFL];
       ALL_TAC] THEN SUBGOAL_THEN `~(&1 - (p:real) = &0)` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     ASM_SIMP_TAC[RPOW_ZERO; REAL_MUL_RZERO; SUM_0; REAL_LE_REFL];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < sum s (x:A->real) /\ &0 < sum s (a:A->real)`
     STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ABBREV_TAC `X = sum s (x:A->real)` THEN
  ABBREV_TAC `A = sum s (a:A->real)` THEN
  (SUBGOAL_THEN `&0 < X rpow p * A rpow (&1 - p)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LT THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `sum s (\i:A. x i rpow p * a i rpow (&1 - p)) =
      (X rpow p * A rpow (&1 - p)) *
      sum s (\i. (x i / X) rpow p * (a i / A) rpow (&1 - p))`
     SUBST1_TAC THENL
    [ASM_SIMP_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_DIV] THEN
     SUBGOAL_THEN `&0 < X rpow p /\ &0 < A rpow (&1 - p)` MP_TAC THENL
      [CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[];
       CONV_TAC REAL_FIELD];
     ALL_TAC]) THEN GEN_REWRITE_TAC RAND_CONV[GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  (TRANS_TAC REAL_LE_TRANS
     `sum s (\i:A. p * (x i / X) + (&1 - p) * (a i / A))` THEN CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC RPOW_MUL_RPOW_LE_WEIGHTED_SUM THEN
     ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; real_div; SUM_RMUL; ETA_AX] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

let RADON_INEQUALITY_REV = prove
 (`!s:A->bool x a p.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ &0 <= a i) /\ &0 <= p /\ p <= &1
     ==> sum s (\i. x i rpow p / a i rpow (p - &1)) <=
         sum s x rpow p / sum s a rpow (p - &1)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(p:real) - &1 = --(&1 - p)`] THEN
  REWRITE_TAC[RPOW_NEG; real_div; REAL_INV_INV] THEN
  MATCH_MP_TAC SUM_RPOW_MUL_RPOW_LE THEN ASM_REWRITE_TAC[]);;

let RADON_INEQUALITY = prove
 (`!s:A->bool x a p.
     FINITE s /\
     (!i. i IN s
          ==> &0 <= x i /\ &0 <= a i /\ (&1 < p ==> a i = &0 ==> x i = &0)) /\
     &1 <= p
     ==> sum s x rpow p / sum s a rpow (p - &1) <=
         sum s (\i. x i rpow p / a i rpow (p - &1))`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `p = &1` THENL
    [ASM_REWRITE_TAC[REAL_SUB_REFL; RPOW_0; real_div; REAL_INV_1; REAL_MUL_RID;
                     RPOW_POW; REAL_POW_1; ETA_AX; REAL_LE_REFL];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&1 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(p:real) - &1 = --(&1 - p)`] THEN
  REWRITE_TAC[RPOW_NEG; real_div; REAL_INV_INV] THEN
  SUBGOAL_THEN
    `!i:A. i IN s
           ==> (x i rpow p * a i rpow (&1 - p)) rpow (&1 / p) *
               a i rpow (&1 - &1 / p) =
               x i`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    (SUBGOAL_THEN `~((p:real) = &0) /\ ~(&1 / p = &0)` STRIP_ASSUME_TAC THENL
      [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN ASM_CASES_TAC `(a:A->real) i = &0` THENL
     [SUBGOAL_THEN `(x:A->real) i = &0` ASSUME_TAC THENL
       [ASM_MESON_TAC[];
        ALL_TAC] THEN ASM_REWRITE_TAC[RPOW_ZERO; REAL_MUL_LZERO];
      SUBGOAL_THEN `&0 < (a:A->real) i` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; GSYM REAL_MUL_ASSOC;
                   GSYM RPOW_ADD] THEN
      (SUBGOAL_THEN
         `(p:real) * &1 / p = &1 /\ (&1 - p) * &1 / p + &1 - &1 / p = &0`
         (fun th -> REWRITE_TAC[th]) THENL
        [UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
         REWRITE_TAC[RPOW_0; REAL_MUL_RID; RPOW_POW; REAL_POW_1]])];
    SUBGOAL_THEN
      `&0 <= sum s (\i:A. x i rpow p * a i rpow (&1 - p)) /\
       &0 <= sum s (a:A->real) /\ &0 <= sum s (x:A->real)`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE];
      ALL_TAC] THEN
    (MP_TAC(ISPECL[`s:A->bool`;
                   `\i:A. (x:A->real) i rpow p * (a:A->real) i rpow (&1 - p)`;
                   `a:A->real`; `&1 / (p:real)`] SUM_RPOW_MUL_RPOW_LE) THEN
     ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE] THEN ANTS_TAC THENL
      [CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
         ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 < p ==> &0 < p`] THEN
         ASM_REAL_ARITH_TAC];
       ALL_TAC]) THEN
    (SUBGOAL_THEN
       `sum s (\i:A. (x i rpow p * a i rpow (&1 - p)) rpow (&1 / p) *
                     a i rpow (&1 - &1 / p)) =
        sum s x`
       SUBST1_TAC THENL
      [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
       DISCH_TAC]) THEN
    ABBREV_TAC `Y = sum s (\i:A. x i rpow p * a i rpow (&1 - p))` THEN
    ABBREV_TAC `A = sum s (a:A->real)` THEN
    ABBREV_TAC `X = sum s (x:A->real)` THEN
    (ASM_CASES_TAC `A = &0` THENL
      [SUBGOAL_THEN `~(&1 - (p:real) = &0)` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN ASM_REWRITE_TAC[RPOW_ZERO; REAL_MUL_RZERO];
       ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (MP_TAC(ISPECL[`X:real`; `Y rpow (&1 / p) * A rpow (&1 - &1 / p)`;
                   `p:real`] RPOW_LE2) THEN ASM_REWRITE_TAC[] THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; REAL_LT_IMP_LE] THEN
     SUBGOAL_THEN `&1 / (p:real) * p = &1 /\ (&1 - &1 / p) * p = p - &1`
       (fun th -> REWRITE_TAC[th]) THENL
      [UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
       REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN DISCH_TAC]) THEN
    MP_TAC(ISPECL[`X rpow p`; `Y * A rpow (p - &1)`; `A rpow (&1 - p)`]
             REAL_LE_RMUL) THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; GSYM RPOW_ADD;
                 REAL_ARITH `((p:real) - &1) + (&1 - p) = &0`; RPOW_0;
                 REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* Hoelder's inequality for p, q > 0 with 1/p + 1/q = 1, and Minkowski's     *)
(* inequality for p >= 1, for sums over any finite index set.                *)
(* ------------------------------------------------------------------------- *)

let HOELDER_SUM_INEQUALITY = prove
 (`!s:A->bool x y p q.
     FINITE s /\ &0 < p /\ &0 < q /\ inv p + inv q = &1
     ==> sum s (\i. abs(x i * y i)) <=
         sum s (\i. abs(x i) rpow p) rpow (&1 / p) *
         sum s (\i. abs(y i) rpow q) rpow (&1 / q)`,
  REPEAT STRIP_TAC THEN
  (MP_TAC(ISPECL[`s:A->bool`; `\i:A. abs((x:A->real) i) rpow p`;
                 `\i:A. abs((y:A->real) i) rpow q`; `&1 / (p:real)`]
            SUM_RPOW_MUL_RPOW_LE) THEN
   ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN ANTS_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     MP_TAC(SPEC `q:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&1 - &1 / (p:real) = &1 / q` SUBST1_TAC THENL
    [REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_ABS_POS; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; real_div; REAL_MUL_LID;
               REAL_MUL_RINV] THEN REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let HOELDER_SUM_RPOW_CONJUGATE = prove
 (`!s:A->bool z w p.
     FINITE s /\ &1 < p
     ==> sum s (\i. abs(z i) * abs(w i) rpow (p - &1)) <=
         sum s (\i. abs(z i) rpow p) rpow (&1 / p) *
         sum s (\i. abs(w i) rpow p) rpow ((p - &1) / p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `z:A->real`;
                 `\i:A. abs((w:A->real) i) rpow (p - &1)`; `p:real`;
                 `(p:real) / (p - &1)`] HOELDER_SUM_INEQUALITY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SIMP_TAC[REAL_ABS_MUL; RPOW_POS_LE; REAL_ABS_POS; REAL_ABS_ABS;
           RPOW_RPOW] THEN
  SUBGOAL_THEN `!t e. abs(abs t rpow e) = abs t rpow e`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_REFL] THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SIMP_TAC[RPOW_RPOW; REAL_ABS_POS] THEN
  SUBGOAL_THEN
   `((p:real) - &1) * p / (p - &1) = p /\ &1 / (p / (p - &1)) = (p - &1) / p`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD);;

let MINKOWSKI_INEQUALITY = prove
 (`!s:A->bool x y p.
     FINITE s /\ &1 <= p
     ==> sum s (\i. abs(x i + y i) rpow p) rpow (&1 / p) <=
         sum s (\i. abs(x i) rpow p) rpow (&1 / p) +
         sum s (\i. abs(y i) rpow p) rpow (&1 / p)`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `p = &1` THENL
    [ASM_REWRITE_TAC[REAL_DIV_1; RPOW_POW; REAL_POW_1; ETA_AX] THEN
     ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
     ASM_REWRITE_TAC[REAL_ABS_TRIANGLE];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&1 < p /\ &0 < p` STRIP_ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN ABBREV_TAC `S = sum s (\i:A. abs(x i + y i) rpow p)` THEN
  ABBREV_TAC `A = sum s (\i:A. abs(x i) rpow p) rpow (&1 / p)` THEN
  ABBREV_TAC `B = sum s (\i:A. abs(y i) rpow p) rpow (&1 / p)` THEN
  (SUBGOAL_THEN `&0 <= S /\ &0 <= A /\ &0 <= B` STRIP_ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC["S"; "A"; "B"] THEN REPEAT CONJ_TAC THEN
     TRY(MATCH_MP_TAC RPOW_POS_LE) THEN MATCH_MP_TAC SUM_POS_LE THEN
     REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN
     REWRITE_TAC[REAL_ABS_POS];
     ALL_TAC]) THEN
  SUBGOAL_THEN
    `!z:A->real. sum s (\i. abs(z i) * abs(x i + y i) rpow (p - &1))
                 <= sum s (\i. abs(z i) rpow p) rpow (&1 / p) *
                    S rpow ((p - &1) / p)`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`s:A->bool`; `z:A->real`; `\i:A. (x:A->real) i + y i`;
                   `p:real`] HOELDER_SUM_RPOW_CONJUGATE) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `S <= (A + B) * S rpow ((p - &1) / p)` ASSUME_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
        `sum s (\i:A. abs(x i) * abs(x i + y i) rpow (p - &1)) +
         sum s (\i. abs(y i) * abs(x i + y i) rpow (p - &1))` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "S" THEN ASM_SIMP_TAC[GSYM SUM_ADD] THEN EXPAND_TAC "S" THEN
        MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN
        GEN_REWRITE_TAC(LAND_CONV o RAND_CONV)
          [REAL_ARITH `(p:real) = &1 + (p - &1)`] THEN
        SIMP_TAC[RPOW_ADD_ALT; REAL_ABS_POS;
                 REAL_ARITH `&1 + ((p:real) - &1) = p`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ; RPOW_POW; REAL_POW_1] THEN
        (SUBGOAL_THEN `!t. &0 <= t ==> t rpow p = t * t rpow (p - &1)`
           (fun th -> SIMP_TAC[th; REAL_ABS_POS]) THENL
          [REPEAT STRIP_TAC THEN
           MP_TAC(ISPECL[`t:real`; `&1`; `(p:real) - &1`] RPOW_ADD_ALT) THEN
           ASM_REWRITE_TAC[REAL_ARITH `&1 + ((p:real) - &1) = p`; RPOW_POW;
                           REAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
           ASM_REAL_ARITH_TAC;
           ALL_TAC]) THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS; REAL_ABS_TRIANGLE];
        MAP_EVERY EXPAND_TAC["A"; "B"] THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `S = &0` THENL
       [SUBGOAL_THEN `~(&1 / (p:real) = &0)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN ASM_REWRITE_TAC[RPOW_ZERO] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      (SUBGOAL_THEN `&0 < S /\ &0 < S rpow ((p - &1) / p)`
         STRIP_ASSUME_TAC THENL
        [CONJ_TAC THENL
          [ASM_REAL_ARITH_TAC;
           MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC];
         ALL_TAC]) THEN
      (SUBGOAL_THEN `S = S rpow (&1 / p) * S rpow ((p - &1) / p)` MP_TAC THENL
        [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
         SUBGOAL_THEN `&1 / (p:real) + (p - &1) / p = &1` SUBST1_TAC THENL
          [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
           REWRITE_TAC[RPOW_POW; REAL_POW_1]];
         ALL_TAC]) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC
                   `S <= (A + B) * S rpow ((p - &1) / p)` THEN
                 GEN_REWRITE_TAC(LAND_CONV o LAND_CONV) [th]) THEN
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ]]]);;

(* ------------------------------------------------------------------------- *)
(* Power means M_p = (sum w_i |x_i|^p)^(1/p) for weights w_i >= 0 with sum   *)
(* w_i = 1, and M_0 = prod |x_i|^w_i. M_p <= M_q for p <= q, where p < 0     *)
(* needs x_i <> 0 whenever w_i > 0. Over {i | w_i > 0}: min |x_i| <= M_p,    *)
(* and M_p <= max |x_i| (for p < 0 only when x_i <> 0 wherever w_i > 0); M_p *)
(* tends to max |x_i| as p -> +oo, to min |x_i| as p -> -oo when x_i <> 0    *)
(* wherever w_i > 0, and to M_0 as p -> 0 (from the right for every x, from  *)
(* both sides when x_i <> 0 wherever w_i > 0). The sheet's limits min x_i    *)
(* and max x_i are false for x = (-2, 1), w = (1/2, 1/2).                    *)
(* ------------------------------------------------------------------------- *)

let power_mean = new_definition
 `power_mean (s:A->bool) w x p =
    if p = &0 then product s (\i. abs(x i) rpow w i)
    else sum s (\i. w i * abs(x i) rpow p) rpow (&1 / p)`;;

let POWER_MEAN_INV = prove
 (`!s:A->bool w x p. FINITE s
     ==> power_mean s w (\i. inv(x i)) (--p) = inv(power_mean s w x p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[power_mean; REAL_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_ABS_INV; RPOW_INV; PRODUCT_INV; RPOW_NEG;
               REAL_INV_INV] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_NEG; RPOW_NEG]);;

let POWER_MEAN_MONO_POS = prove
 (`!s:A->bool w x p q.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 < p /\ p <= q
     ==> power_mean s w x p <= power_mean s w x q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ ~(p = &0) /\ ~(q = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_REWRITE_TAC[power_mean] THEN
  (MP_TAC(ISPECL[`s:A->bool`;
                 `\i:A. (w:A->real) i * abs((x:A->real) i) rpow q`;
                 `w:A->real`; `(p:real) / q`] SUM_RPOW_MUL_RPOW_LE) THEN
   ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS] THEN ANTS_TAC THENL
    [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN REWRITE_TAC[RPOW_ONE; REAL_MUL_RID] THEN
  (SUBGOAL_THEN
     `sum s
        (\i:A. (w i * abs(x i) rpow q) rpow (p / q) * w i rpow (&1 - p / q)) =
      sum s (\i. w i * abs(x i) rpow p)`
     SUBST1_TAC THENL
    [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
     SUBGOAL_THEN `&0 <= (w:A->real) i` MP_TAC THENL
      [ASM_SIMP_TAC[];
       ALL_TAC] THEN REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
      [ALL_TAC;
       FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
       SUBGOAL_THEN `~((p:real) / q = &0)` ASSUME_TAC THENL
        [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
         ASM_REWRITE_TAC[];
         ASM_REWRITE_TAC[REAL_MUL_LZERO; RPOW_ZERO]]] THEN
     ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; REAL_ABS_POS; REAL_DIV_LMUL] THEN
     ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = (a * c) * b:real`] THEN
     ASM_SIMP_TAC[GSYM RPOW_ADD; REAL_ARITH `(x:real) + &1 - x = &1`; RPOW_POW;
                  REAL_POW_1];
     ALL_TAC]) THEN
  (DISCH_TAC THEN
   SUBGOAL_THEN
     `&0 <= sum s (\i:A. w i * abs(x i) rpow p) /\
      &0 <= sum s (\i:A. w i * abs(x i) rpow q)`
     STRIP_ASSUME_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
     ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`sum s (\i:A. w i * abs(x i) rpow p)`;
                `sum s (\i:A. w i * abs(x i) rpow q) rpow (p / q)`;
                `&1 / (p:real)`] RPOW_LE2) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; RPOW_RPOW] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) = c ==> a <= b ==> a <= c`) THEN
  AP_TERM_TAC THEN UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < q` THEN
  CONV_TAC REAL_FIELD);;

let POWER_MEAN_ZERO_LE = prove
 (`!s:A->bool w x q.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 < q
     ==> power_mean s w x (&0) <= power_mean s w x q`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[power_mean; REAL_LT_IMP_NZ] THEN
  MP_TAC(ISPECL[`w:A->real`; `\i:A. abs((x:A->real) i) rpow q`; `s:A->bool`]
           AGM_GEN) THEN
  ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS; RPOW_RPOW] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM RPOW_RPOW; REAL_ABS_POS] THEN
  ASM_SIMP_TAC[GSYM RPOW_PRODUCT] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `&0 <= product s (\i:A. abs(x i) rpow w i)` ASSUME_TAC THENL
    [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`product s (\i:A. abs((x:A->real) i) rpow (w:A->real) i) rpow
                 q`;
                `sum s (\i:A. abs((x:A->real) i) rpow q * (w:A->real) i)`;
                `&1 / (q:real)`] RPOW_LE2) THEN
  ASM_SIMP_TAC[RPOW_POS_LE; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
               RPOW_RPOW] THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_RINV; REAL_LT_IMP_NZ; RPOW_POW;
               REAL_POW_1]);;

let POWER_MEAN_POS_LT = prove
 (`!s:A->bool w x p.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\
     (!i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> &0 < power_mean s w x p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[power_mean] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(w:A->real) i = &0` THEN
    ASM_REWRITE_TAC[RPOW_0; REAL_LT_01] THEN MATCH_MP_TAC RPOW_POS_LT THEN
    REWRITE_TAC[GSYM REAL_ABS_NZ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_LE];
    MATCH_MP_TAC RPOW_POS_LT THEN MATCH_MP_TAC SUM_POS_LT THEN
    ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS] THEN
    (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
      [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
       UNDISCH_TAC `sum s (w:A->real) = &1` THEN
       MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
       MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
       ALL_TAC]) THEN EXISTS_TAC `j:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_POS_LT THEN REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    ASM_SIMP_TAC[]]);;

let POWER_MEAN_MONO = prove
 (`!s:A->bool w x p q.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ p <= q /\
     (p < &0 ==> !i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> power_mean s w x p <= power_mean s w x q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN
     `!z:A->real a b. &0 <= a /\ a <= b
                      ==> power_mean s w z a <= power_mean s w z b`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN ASM_CASES_TAC `a = &0` THENL
      [ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
       MATCH_MP_TAC POWER_MEAN_ZERO_LE THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC;
       MATCH_MP_TAC POWER_MEAN_MONO_POS THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `!a b. a <= b /\ b <= &0 /\ (!i:A. i IN s /\ &0 < w i ==> ~(x i = &0))
            ==> power_mean s w x a <= power_mean s w x b`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. inv((x:A->real) i)`]
              POWER_MEAN_INV) THEN ASM_REWRITE_TAC[REAL_INV_INV; ETA_AX] THEN
     DISCH_TAC THEN
     GEN_REWRITE_TAC(LAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
     GEN_REWRITE_TAC(RAND_CONV o RAND_CONV) [GSYM REAL_NEG_NEG] THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
      [MATCH_MP_TAC POWER_MEAN_POS_LT THEN ASM_SIMP_TAC[REAL_INV_EQ_0];
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `&0 <= p` THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `p < &0`
     (fun th -> ASSUME_TAC th THEN FIRST_X_ASSUM(ASSUME_TAC o C MP th)) THENL
    [ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (ASM_CASES_TAC `q <= &0` THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
  (TRANS_TAC REAL_LE_TRANS `power_mean s (w:A->real) x (&0)` THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC(ASSUME
                    `!z:A->real a b. &0 <= a /\ a <= b
                                     ==> power_mean s w z a
                                         <= power_mean s w z b`) THEN
     ASM_REAL_ARITH_TAC]));;

let POWER_MEAN_GE_NONNEG = prove
 (`!s:A->bool w x p a.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 <= p /\
     &0 <= a /\
     (!i. i IN s /\ &0 < w i ==> a <= abs(x i))
     ==> a <= power_mean s w x p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!i:A. i IN s
           ==> w i * a rpow p <= w i * abs(x i) rpow p /\
               a rpow w i <= abs(x i) rpow w i`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (w:A->real) i` MP_TAC THENL
     [ASM_SIMP_TAC[];
      ALL_TAC] THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
     [ALL_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_MUL_LZERO; RPOW_0; REAL_LE_REFL]] THEN
    (SUBGOAL_THEN `a <= abs((x:A->real) i)` ASSUME_TAC THENL
      [ASM_SIMP_TAC[];
       ALL_TAC] THEN CONJ_TAC THEN
     TRY(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [ASM_SIMP_TAC[REAL_LT_IMP_LE];
           ALL_TAC]) THEN MATCH_MP_TAC RPOW_LE2 THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE]);
    REWRITE_TAC[power_mean] THEN COND_CASES_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `product s (\i:A. a rpow w i)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[RPOW_POS_LE]] THEN
      (ASM_CASES_TAC `a = &0` THENL
        [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
         ASM_SIMP_TAC[RPOW_POS_LE; REAL_LE_REFL];
         ALL_TAC]) THEN
      (SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN ASM_SIMP_TAC[rpow; GSYM REAL_EXP_SUM; SUM_RMUL] THEN
       ASM_SIMP_TAC[REAL_MUL_LID; EXP_LOG; REAL_LE_REFL]);
      SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      (SUBGOAL_THEN `a rpow p <= sum s (\i:A. w i * abs(x i) rpow p)`
         ASSUME_TAC THENL
        [TRANS_TAC REAL_LE_TRANS `sum s (\i:A. w i * a rpow p)` THEN
         CONJ_TAC THENL
          [ASM_SIMP_TAC[SUM_RMUL; REAL_MUL_LID; REAL_LE_REFL];
           MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[]];
         ALL_TAC]) THEN
      MP_TAC(ISPECL[`a rpow p`; `sum s (\i:A. w i * abs(x i) rpow p)`;
                    `&1 / (p:real)`] RPOW_LE2) THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
                   RPOW_RPOW; REAL_DIV_LMUL; REAL_LT_IMP_NZ; real_div;
                   REAL_MUL_LID; REAL_MUL_RINV; RPOW_POW; REAL_POW_1]]]);;

let POWER_MEAN_LE_NONNEG = prove
 (`!s:A->bool w x p b.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 <= p /\
     &0 <= b /\
     (!i. i IN s /\ &0 < w i ==> abs(x i) <= b)
     ==> power_mean s w x p <= b`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN
     `!i:A. i IN s
            ==> w i * abs(x i) rpow p <= w i * b rpow p /\
                abs(x i) rpow w i <= b rpow w i`
     ASSUME_TAC THENL
    [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (w:A->real) i` MP_TAC THENL
      [ASM_SIMP_TAC[];
       ALL_TAC] THEN
     DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
      [ALL_TAC;
       FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[REAL_MUL_LZERO; RPOW_0; REAL_LE_REFL]] THEN
     SUBGOAL_THEN `abs((x:A->real) i) <= b` ASSUME_TAC THENL
      [ASM_SIMP_TAC[];
       ALL_TAC] THEN CONJ_TAC THEN
     TRY(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
          [ASM_SIMP_TAC[REAL_LT_IMP_LE];
           ALL_TAC]) THEN MATCH_MP_TAC RPOW_LE2 THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN REWRITE_TAC[power_mean] THEN COND_CASES_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `product s (\i:A. b rpow w i)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
      ALL_TAC] THEN
    (ASM_CASES_TAC `b = &0` THENL
      [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
       ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `j:A` THEN
       ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ];
       ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[rpow; GSYM REAL_EXP_SUM; SUM_RMUL] THEN
     ASM_SIMP_TAC[REAL_MUL_LID; EXP_LOG; REAL_LE_REFL]);
    SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    (SUBGOAL_THEN `sum s (\i:A. w i * abs(x i) rpow p) <= b rpow p`
       ASSUME_TAC THENL
      [TRANS_TAC REAL_LE_TRANS `sum s (\i:A. w i * b rpow p)` THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[];
         ASM_SIMP_TAC[SUM_RMUL; REAL_MUL_LID; REAL_LE_REFL]];
       ALL_TAC]) THEN
    (MP_TAC(ISPECL[`sum s (\i:A. w i * abs(x i) rpow p)`; `b rpow p`;
                   `&1 / (p:real)`] RPOW_LE2) THEN ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE THEN
         ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS];
         MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
       ALL_TAC] THEN
     ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; real_div; REAL_MUL_LID;
                  REAL_MUL_RINV; REAL_LT_IMP_NZ; RPOW_POW; REAL_POW_1])]);;

let POWER_MEAN_POS_LE = prove
 (`!s:A->bool w x p.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) ==> &0 <= power_mean s w x p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[power_mean] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
    MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS]]);;

let POWER_MEAN_GE = prove
 (`!s:A->bool w x p a.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 <= a /\
     (!i. i IN s /\ &0 < w i ==> a <= abs(x i))
     ==> a <= power_mean s w x p`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `&0 <= p` THENL
    [MATCH_MP_TAC POWER_MEAN_GE_NONNEG THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `a = &0` THENL
    [ASM_SIMP_TAC[POWER_MEAN_POS_LE];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. inv((x:A->real) i)`;
                `--p:real`] POWER_MEAN_INV) THEN
  ASM_REWRITE_TAC[REAL_INV_INV; ETA_AX; REAL_NEG_NEG] THEN
  DISCH_THEN SUBST1_TAC THEN
  (SUBGOAL_THEN `!i:A. i IN s /\ &0 < w i ==> &0 < abs(x i)` ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN TRANS_TAC REAL_LTE_TRANS `a:real` THEN
     ASM_SIMP_TAC[];
     ALL_TAC]) THEN
  (GEN_REWRITE_TAC LAND_CONV[GSYM REAL_INV_INV] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
    [MATCH_MP_TAC POWER_MEAN_POS_LT THEN
     ASM_SIMP_TAC[REAL_INV_EQ_0; GSYM REAL_ABS_NZ];
     ALL_TAC]) THENL
   [ASM_MESON_TAC[REAL_ABS_NZ];
    MATCH_MP_TAC POWER_MEAN_LE_NONNEG THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[]]);;

let POWER_MEAN_LE = prove
 (`!s:A->bool w x p b.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\ &0 <= b /\
     (!i. i IN s /\ &0 < w i ==> abs(x i) <= b) /\
     (p < &0 ==> !i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> power_mean s w x p <= b`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `&0 <= p` THENL
    [MATCH_MP_TAC POWER_MEAN_LE_NONNEG THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ANTS_TAC THENL
    [ASM_REAL_ARITH_TAC;
     DISCH_TAC]) THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
    [TRANS_TAC REAL_LTE_TRANS `abs((x:A->real) j)` THEN
     ASM_SIMP_TAC[GSYM REAL_ABS_NZ];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. inv((x:A->real) i)`;
                `--p:real`] POWER_MEAN_INV) THEN
  ASM_REWRITE_TAC[REAL_INV_INV; ETA_AX; REAL_NEG_NEG] THEN
  DISCH_THEN SUBST1_TAC THEN GEN_REWRITE_TAC RAND_CONV[GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  (MATCH_MP_TAC POWER_MEAN_GE_NONNEG THEN
   ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_INV] THEN
   MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[GSYM REAL_ABS_NZ]));;

let POWER_MEAN_BOUNDS = prove
 (`!s:A->bool w x p.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1
     ==> inf {abs(x i) | i IN s /\ &0 < w i} <= power_mean s w x p /\
         ((p < &0 ==> !i. i IN s /\ &0 < w i ==> ~(x i = &0))
          ==> power_mean s w x p <= sup {abs(x i) | i IN s /\ &0 < w i})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `FINITE {abs((x:A->real) i) | i IN s /\ &0 < w i} /\
      ~({abs((x:A->real) i) | i IN s /\ &0 < w i} = {})`
     STRIP_ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
     ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `j:A` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC POWER_MEAN_GE THEN
     ASM_SIMP_TAC[REAL_LE_INF_FINITE; REAL_INF_LE_FINITE] THEN
     REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC[REAL_ABS_POS];
       EXISTS_TAC `abs((x:A->real) i)` THEN REWRITE_TAC[REAL_LE_REFL] THEN
       EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[]];
     ALL_TAC]) THEN
  (DISCH_TAC THEN MATCH_MP_TAC POWER_MEAN_LE THEN
   ASM_SIMP_TAC[REAL_LE_SUP_FINITE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   CONJ_TAC THENL
    [EXISTS_TAC `abs((x:A->real) j)` THEN REWRITE_TAC[REAL_ABS_POS] THEN
     EXISTS_TAC `j:A` THEN ASM_REWRITE_TAC[];
     REPEAT STRIP_TAC THEN EXISTS_TAC `abs((x:A->real) i)` THEN
     REWRITE_TAC[REAL_LE_REFL] THEN EXISTS_TAC `i:A` THEN
     ASM_REWRITE_TAC[]]));;

let POWER_MEAN_LIMIT_POSINF = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1
     ==> ((\p. power_mean s w x p) ---> sup {abs(x i) | i IN s /\ &0 < w i})
         at_posinfinity`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `FINITE {abs((x:A->real) i) | i IN s /\ &0 < w i} /\
      ~({abs((x:A->real) i) | i IN s /\ &0 < w i} = {})`
     STRIP_ASSUME_TAC THENL
    [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
     ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `j:A` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPEC `{abs((x:A->real) i) | i IN s /\ &0 < w i}` SUP_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = sup {abs((x:A->real) i) | i IN s /\ &0 < w i}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)
               ASSUME_TAC) THEN
  (SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[REAL_ABS_POS];
     ALL_TAC]) THEN
  (ABBREV_TAC `L = abs(log((w:A->real) k))` THEN
   SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
    [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_ABS_POS];
     ALL_TAC]) THEN REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `((M:real) * L + &1) / e + &1` THEN X_GEN_TAC `p:real` THEN
  REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `&0 <= ((M:real) * L + &1) / e` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_MUL;
                  REAL_ARITH `&0 <= x ==> &0 <= x + &1`];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `power_mean s w (x:A->real) p <= M` ASSUME_TAC THENL
    [MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `x:A->real`; `p:real`]
              POWER_MEAN_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `(w:A->real) k * M rpow p <= sum s (\i. w i * abs((x:A->real) i) rpow p)`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL[`{k:A}`; `s:A->bool`;
                   `\i:A. (w:A->real) i * abs((x:A->real) i) rpow p`]
              SUM_SUBSET_SIMPLE) THEN
     ASM_SIMP_TAC[SUM_SING; SING_SUBSET; IN_DIFF; REAL_LE_MUL; RPOW_POS_LE;
                  REAL_ABS_POS];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `(w:A->real) k rpow (&1 / p) * M <= power_mean s w (x:A->real) p`
     ASSUME_TAC THENL
    [ASM_SIMP_TAC[power_mean; REAL_LT_IMP_NZ] THEN
     MP_TAC(ISPECL[`(w:A->real) k * M rpow p`;
                   `sum s (\i. (w:A->real) i * abs((x:A->real) i) rpow p)`;
                   `&1 / (p:real)`] RPOW_LE2) THEN
     ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_LT_IMP_LE; REAL_LE_DIV;
                  REAL_POS; RPOW_MUL; RPOW_RPOW] THEN
     ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                  RPOW_POW; REAL_POW_1];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&1 - L / p <= (w:A->real) k rpow (&1 / p)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[rpow] THEN
     TRANS_TAC REAL_LE_TRANS `&1 + &1 / p * log((w:A->real) k)` THEN
     REWRITE_TAC[REAL_EXP_LE_X] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
     MATCH_MP_TAC(REAL_ARITH
                    `--(a * b) <= c * b ==> &1 - a * b <= &1 + b * c`) THEN
     REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
     ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
     UNDISCH_TAC `abs(log((w:A->real) k)) = L` THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `((M:real) * L) / p < e` ASSUME_TAC THENL
    [SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < p`] THEN
     UNDISCH_TAC `((M:real) * L + &1) / e + &1 <= p` THEN
     SIMP_TAC[GSYM REAL_LE_SUB_LADD; REAL_LE_LDIV_EQ; ASSUME `&0 < e`] THEN
     UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `M * (&1 - L / p) <= M * (w:A->real) k rpow (&1 / p)`
     MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  UNDISCH_TAC
    `(w:A->real) k rpow (&1 / p) * M <= power_mean s w (x:A->real) p` THEN
  UNDISCH_TAC `power_mean s w (x:A->real) p <= M` THEN
  UNDISCH_TAC `((M:real) * L) / p < e` THEN
  REWRITE_TAC[real_div; REAL_SUB_LDISTRIB; REAL_MUL_RID; REAL_MUL_ASSOC] THEN
  REAL_ARITH_TAC);;

let POWER_MEAN_LIMIT_NEGINF = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\
     (!i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> ((\p. power_mean s w x p) ---> inf {abs(x i) | i IN s /\ &0 < w i})
         at_neginfinity`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `!f:A->real. FINITE {f i | i IN s /\ &0 < w i} /\
                  ~({f i | i IN s /\ &0 < w i} = {})`
     ASSUME_TAC THENL
    [GEN_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
     ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
     REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `j:A` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  MP_TAC(ISPEC `{abs((x:A->real) i) | i IN s /\ &0 < w i}` INF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = inf {abs((x:A->real) i) | i IN s /\ &0 < w i}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)
               ASSUME_TAC) THEN
  (SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
    [ASM_SIMP_TAC[GSYM REAL_ABS_NZ];
     ALL_TAC]) THEN
  SUBGOAL_THEN `sup {abs(inv((x:A->real) i)) | i IN s /\ &0 < w i} = inv m`
    ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o ISPEC
                  `\i:A. abs(inv((x:A->real) i))` o
                  check(is_forall o concl)) THEN
    ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_SIMP_TAC[REAL_SUP_LE_FINITE; REAL_LE_SUP_FINITE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    (CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
       MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
        [ASM_MESON_TAC[];
         UNDISCH_TAC `m = abs((x:A->real) k)` THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
         EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[]];
       EXISTS_TAC `abs(inv((x:A->real) k))` THEN
       REWRITE_TAC[REAL_ABS_INV; REAL_LE_REFL] THEN EXISTS_TAC `k:A` THEN
       ASM_REWRITE_TAC[REAL_ABS_INV]]);
    MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. inv((x:A->real) i)`]
             POWER_MEAN_LIMIT_POSINF) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ] REALLIM_INV)) THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; REAL_INV_INV] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC]) THEN
    (REWRITE_TAC[REALLIM_AT_POSINFINITY; REALLIM_AT_NEGINFINITY; real_ge] THEN
     DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN EXISTS_TAC `--b:real` THEN
     X_GEN_TAC `p:real` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `--p:real`) THEN ANTS_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    MP_TAC(ISPECL[`s:A->bool`; `w:A->real`; `\i:A. inv((x:A->real) i)`;
                  `--p:real`] POWER_MEAN_INV) THEN
    ASM_REWRITE_TAC[REAL_INV_INV; ETA_AX; REAL_NEG_NEG] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let POWER_MEAN_LIMIT_ZERO = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\
     (!i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> ((\p. power_mean s w x p) ---> power_mean s w x (&0)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `S = \p. sum s (\i:A. w i * exp(p * log(abs((x:A->real) i))))` THEN
  (SUBGOAL_THEN
     `!p i:A. i IN s
              ==> w i * abs((x:A->real) i) rpow p =
                  w i * exp(p * log(abs(x i))) /\
                  abs(x i) rpow w i = exp(w i * log(abs(x i)))`
     ASSUME_TAC THENL
    [REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `(w:A->real) i = &0` THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO; RPOW_0; REAL_EXP_0] THEN
     SUBGOAL_THEN `&0 < abs((x:A->real) i)` ASSUME_TAC THENL
      [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[];
       ASM_REWRITE_TAC[rpow]];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `!p. sum s (\i:A. w i * abs((x:A->real) i) rpow p) = S p`
     ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `power_mean s w (x:A->real) (&0) = exp(sum s (\i. w i * log(abs(x i))))`
     SUBST1_TAC THENL
    [ASM_SIMP_TAC[power_mean; REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_EQ THEN
     ASM_SIMP_TAC[];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `?j:A. j IN s /\ &0 < w j` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
     UNDISCH_TAC `sum s (w:A->real) = &1` THEN
     MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x = &1 ==> F`) THEN
     MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_NOT_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `!p. &0 < (S:real->real) p` ASSUME_TAC THENL
    [GEN_TAC THEN EXPAND_TAC "S" THEN BETA_TAC THEN
     MATCH_MP_TAC SUM_POS_LT THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE] THEN EXISTS_TAC `j:A` THEN
     ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
     ALL_TAC]) THEN
  (SUBGOAL_THEN `(S:real->real)(&0) = &1` ASSUME_TAC THENL
    [EXPAND_TAC "S" THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_RID; ETA_AX];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `((S:real->real)
       has_real_derivative sum s (\i:A. w i * log(abs((x:A->real) i))))
      (atreal (&0))`
     ASSUME_TAC THENL
    [EXPAND_TAC "S" THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
     ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0] THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  MP_TAC(INST[`inv:real->real`, `g':real->real`;
              `sum s (\i:A. w i * log(abs((x:A->real) i)))`, `f':real`]
           (ISPECL[`\x:real. &0 < x`; `S:real->real`; `log`]
              HAS_REAL_DERIVATIVE_CHAIN)) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_LOG] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_INV_1; REAL_MUL_RID] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; LOG_1; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[LOG_1; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_REAL_CONTINUOUS_FUNCTION o
               CONJ(ISPEC `sum s (\i:A. w i * log(abs((x:A->real) i)))`
                      REAL_CONTINUOUS_AT_EXP)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1` THEN
  REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO; GSYM REAL_ABS_NZ] THEN
  X_GEN_TAC `p:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[power_mean] THEN
  ASM_SIMP_TAC[rpow] THEN REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_SYM]);;

let SUM_MUL_ABS_RPOW_LE_LINEAR = prove
 (`!s:A->bool w x j p.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1 /\
     j IN s /\ x j = &0 /\ &0 < p /\ p <= &1
     ==> sum s (\i. w i * abs(x i) rpow p) <=
         &1 - w j + p * sum s (\i. w i * abs(x i))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum s (\i:A. w i * (&1 + p * abs((x:A->real) i))) - w j` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; SUM_ADD; REAL_MUL_RID; ETA_AX] THEN
    REWRITE_TAC[REAL_ARITH `(w:real) * p * a = p * (w * a)`] THEN
    ASM_SIMP_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(a:real) = b ==> (&1 + a) - w <= &1 - w + b`) THEN
    AP_TERM_TAC THEN REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`\i:A. w i * abs((x:A->real) i) rpow p`; `s:A->bool`; `j:A`]
         SUM_DELETE) THEN
  MP_TAC(ISPECL [`\i:A. w i * (&1 + p * abs((x:A->real) i))`; `s:A->bool`;
                 `j:A`] SUM_DELETE) THEN
  ASM_SIMP_TAC[REAL_ABS_0; RPOW_ZERO; REAL_LT_IMP_NZ; REAL_MUL_RZERO;
               REAL_ADD_RID; REAL_MUL_RID; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(c:real) <= d ==> d = b - w ==> c = a ==> a <= b - w`) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  X_GEN_TAC `k:A` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`p:real`; `abs((x:A->real) k)`]
         RPOW_BERNOULLI_TANGENT_REV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS] THEN
  MP_TAC(SPEC `(x:A->real) k` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC);;

let POWER_MEAN_LIMIT_ZERO_RIGHT = prove
 (`!s:A->bool w x.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ sum s w = &1
     ==> ((\p. power_mean s w x p) ---> power_mean s w x (&0))
         (atreal (&0) within {p | &0 < p})`,
  REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `!i:A. i IN s /\ &0 < w i ==> ~(x i = &0)` THENL
    [MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
     MATCH_MP_TAC POWER_MEAN_LIMIT_ZERO THEN ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I[NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
  (SUBGOAL_THEN `power_mean s w (x:A->real) (&0) = &0` SUBST1_TAC THENL
    [ASM_SIMP_TAC[power_mean; PRODUCT_EQ_0] THEN EXISTS_TAC `j:A` THEN
     ASM_SIMP_TAC[REAL_ABS_0; RPOW_ZERO; REAL_LT_IMP_NZ];
     ALL_TAC]) THEN
  (ABBREV_TAC `A = sum s (\i:A. w i * abs((x:A->real) i))` THEN
   SUBGOAL_THEN `&0 <= A /\ (w:A->real) j <= &1` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [EXPAND_TAC "A" THEN MATCH_MP_TAC SUM_POS_LE THEN
       ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS];
       FIRST_X_ASSUM(SUBST1_TAC o SYM o check(fun th -> concl th =
             `sum s (w:A->real) = &1`)) THEN
       MP_TAC(ISPECL[`{j:A}`; `s:A->bool`; `w:A->real`] SUM_SUBSET_SIMPLE) THEN
       ASM_SIMP_TAC[SUM_SING; SING_SUBSET; IN_DIFF]];
     ALL_TAC]) THEN
  SUBGOAL_THEN
    `!p. &0 < p /\ p <= &1
         ==> sum s (\i:A. w i * abs((x:A->real) i) rpow p) <= &1 - w j + p * A`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "A" THEN
    MATCH_MP_TAC SUM_MUL_ABS_RPOW_LE_LINEAR THEN ASM_REWRITE_TAC[];
    ABBREV_TAC `c = &1 - (w:A->real) j / &2` THEN
    SUBGOAL_THEN `&0 < c /\ c < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    (ABBREV_TAC `L = --log c` THEN SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
      [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_NEG_GT0] THEN
       GEN_REWRITE_TAC RAND_CONV[GSYM LOG_1] THEN
       MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
       ALL_TAC]) THEN
    (REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     EXISTS_TAC `min (&1) (min ((w:A->real) j / (&2 * (A + &1))) (e * L))` THEN
     REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN CONJ_TAC THENL
      [CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN X_GEN_TAC `p:real` THEN STRIP_TAC) THEN
    (SUBGOAL_THEN `&0 <= power_mean s w (x:A->real) p` ASSUME_TAC THENL
      [MATCH_MP_TAC POWER_MEAN_POS_LE THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN ASM_SIMP_TAC[real_abs]) THEN
    (SUBGOAL_THEN `sum s (\i:A. w i * abs((x:A->real) i) rpow p) <= c`
       ASSUME_TAC THENL
      [TRANS_TAC REAL_LE_TRANS `&1 - (w:A->real) j + p * A` THEN CONJ_TAC THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN EXPAND_TAC "c" THEN
       UNDISCH_TAC `abs p < (w:A->real) j / (&2 * (A + &1))` THEN
       ASM_SIMP_TAC[REAL_LT_RDIV_EQ;
                    REAL_ARITH `&0 <= A ==> &0 < &2 * (A + &1)`; real_abs;
                    REAL_LT_IMP_LE] THEN DISCH_TAC THEN
       SUBGOAL_THEN `&0 <= p * A` MP_TAC THENL
        [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
         ASM_REAL_ARITH_TAC];
       ALL_TAC]) THEN
    (TRANS_TAC REAL_LET_TRANS `c rpow (&1 / p)` THEN CONJ_TAC THENL
      [ASM_SIMP_TAC[power_mean; REAL_LT_IMP_NZ] THEN MATCH_MP_TAC RPOW_LE2 THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC SUM_POS_LE THEN
         ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS];
         MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
       ALL_TAC]) THEN
    (ASM_SIMP_TAC[rpow] THEN
     SUBGOAL_THEN `&1 / p * log c = --(L / p)` SUBST1_TAC THENL
      [EXPAND_TAC "L" THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
       ALL_TAC]) THEN
    (SUBGOAL_THEN `&0 < L / p` ASSUME_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_DIV];
       ALL_TAC] THEN REWRITE_TAC[REAL_EXP_NEG] THEN
     TRANS_TAC REAL_LET_TRANS `inv(&1 + L / (p:real))` THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN TRANS_TAC REAL_LET_TRANS `(p:real) / L` THEN
    (CONJ_TAC THENL
      [SUBGOAL_THEN `(p:real) / L = inv(L / p)` SUBST1_TAC THENL
        [REWRITE_TAC[REAL_INV_DIV];
         ALL_TAC] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC;
         UNDISCH_TAC `&0 < L / p` THEN REAL_ARITH_TAC];
       SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < L`] THEN
       UNDISCH_TAC `abs p < e * L` THEN UNDISCH_TAC `&0 < p` THEN
       REAL_ARITH_TAC])]);;

let POWER_MEAN_LIMIT_COUNTEREXAMPLE = prove
 (`~(((\p. power_mean {1,2} (\i. &1 / &2) (\i. if i = 1 then -- &2 else &1) p)
      ---> sup {(\i. if i = 1 then -- &2 else &1) i | i IN {1,2}})
     at_posinfinity) /\
   ~(((\p. power_mean {1,2} (\i. &1 / &2) (\i. if i = 1 then -- &2 else &1) p)
      ---> inf {(\i. if i = 1 then -- &2 else &1) i | i IN {1,2}})
     at_neginfinity)`,
  CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`{1,2}`; `\i:num. &1 / &2`;
                   `\i:num. if i = 1 then -- &2 else &1`]
           POWER_MEAN_LIMIT_NEGINF) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; SUM_CLAUSES; IN_INSERT;
               NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `{abs((\i. if i = 1 then -- &2 else &1) i) | i IN {1, 2} /\
       &0 < (\i:num. &1 / &2) i} =
      {&2, &1} /\
      {(\i. if i = 1 then -- &2 else &1) i | i IN {1, 2}} = {-- &2, &1}`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      MP_TAC(REAL_ARITH
       `abs(-- &2) = &2 /\ abs(&1) = &1 /\ &0 < &1 / &2 /\
        ~(&1 = &2) /\ ~(-- &2 = &1)`) THEN
      MP_TAC(ARITH_RULE `~(2 = 1)`) THEN MESON_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(SIMP_RULE[INF_INSERT_FINITE; FINITE_INSERT; FINITE_EMPTY;
                             NOT_INSERT_EMPTY; INF_SING]) THEN
    RULE_ASSUM_TAC(CONV_RULE(REAL_RAT_REDUCE_CONV)) THEN
    POP_ASSUM(fun th2 -> POP_ASSUM(fun th1 -> MP_TAC(MATCH_MP REALLIM_UNIQUE
      (CONJ TRIVIAL_LIMIT_AT_NEGINFINITY (CONJ th1 th2))))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  DISCH_TAC THEN
  (MP_TAC(ISPECL[`{1,2}`; `\i:num. &1 / &2`;
                 `\i:num. if i = 1 then -- &2 else &1`]
            POWER_MEAN_LIMIT_POSINF) THEN ANTS_TAC THENL
    [SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; SUM_CLAUSES; IN_INSERT;
              NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC REAL_RAT_REDUCE_CONV;
     DISCH_TAC]) THEN
  (SUBGOAL_THEN
     `{abs((\i. if i = 1 then -- &2 else &1) i) | i IN {1, 2} /\
       &0 < (\i:num. &1 / &2) i} =
      {&2, &1} /\
      {(\i. if i = 1 then -- &2 else &1) i | i IN {1, 2}} = {-- &2, &1}`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
     MP_TAC(REAL_ARITH
              `abs(-- &2) = &2 /\ abs(&1) = &1 /\ &0 < &1 / &2 /\
               ~(&1 = &2) /\ ~(-- &2 = &1)`) THEN
     MP_TAC(ARITH_RULE `~(2 = 1)`) THEN MESON_TAC[];
     ALL_TAC]) THEN
  RULE_ASSUM_TAC(SIMP_RULE[SUP_INSERT_FINITE; FINITE_INSERT; FINITE_EMPTY;
                           NOT_INSERT_EMPTY; SUP_SING]) THEN
  RULE_ASSUM_TAC(CONV_RULE(REAL_RAT_REDUCE_CONV)) THEN
  POP_ASSUM(fun th2 -> POP_ASSUM(fun th1 -> MP_TAC(MATCH_MP
        REALLIM_UNIQUE(CONJ TRIVIAL_LIMIT_AT_POSINFINITY(CONJ th1 th2))))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Lehmer: sum w_i |x_i|^p / sum w_i |x_i|^(p-1) is nondecreasing in p for   *)
(* w_i >= 0, where p < 1 needs x_i <> 0 whenever w_i > 0. A zero denominator *)
(* gives the value 0, and the inequality holds then too. The core is the     *)
(* similarly ordered sum inequality (SUM_SIMILARLY_ORDERED_LE) for a_i and   *)
(* a_i^r, r >= 0.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_MUL_RPOW_SIMILARLY_LE = prove
 (`!s:A->bool u a r.
     FINITE s /\ (!i. i IN s ==> &0 <= u i /\ &0 <= a i) /\ &0 <= r
     ==> sum s (\i. u i * a i) * sum s (\i. u i * a i rpow r) <=
         sum s u * sum s (\i. u i * a i * a i rpow r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `u:A->real`; `a:A->real`;
                 `\i. (a:A->real) i rpow r`] SUM_SIMILARLY_ORDERED_LE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`(a:A->real) i`; `(a:A->real) j`] REAL_LE_TOTAL) THENL
   [ONCE_REWRITE_TAC[REAL_ARITH
     `((x:real) - y) * (z - w) = (y - x) * (w - z)`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_SUB_LE] THEN CONJ_TAC THEN
  TRY(MATCH_MP_TAC RPOW_LE2) THEN ASM_SIMP_TAC[]);;

let RPOW_LEHMER_TERMS = prove
 (`!a p q. &0 <= a /\ p <= q /\ (a = &0 ==> &1 <= p)
         ==> a rpow (p - &1) * a = a rpow p /\
             a rpow (p - &1) * a rpow (q - p) = a rpow (q - &1) /\
             a rpow (p - &1) * a * a rpow (q - p) = a rpow q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (ASM_CASES_TAC `a = &0` THENL
    [FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN
     ASM_REWRITE_TAC[RPOW_ZERO; REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
     DISCH_TAC THEN
     REPEAT(COND_CASES_TAC THEN
            ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID]) THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MP_TAC(SPECL[`a:real`; `(p:real) - &1`; `&1:real`] RPOW_ADD) THEN
  MP_TAC(SPECL[`a:real`; `(p:real) - &1`; `(q:real) - p`] RPOW_ADD) THEN
  MP_TAC(SPECL[`a:real`; `(p:real) - &1 + &1`; `(q:real) - p`] RPOW_ADD) THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_ARITH `(p:real) - &1 + &1 = p`;
                  REAL_ARITH `(p:real) - &1 + q - p = q - &1`;
                  REAL_ARITH `(p:real) + q - p = q`] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LEHMER_INEQUALITY = prove
 (`!s:A->bool w x p q.
     FINITE s /\ (!i. i IN s ==> &0 <= w i) /\ p <= q /\
     (p < &1 ==> !i. i IN s /\ &0 < w i ==> ~(x i = &0))
     ==> sum s (\i. w i * abs(x i) rpow p) /
         sum s (\i. w i * abs(x i) rpow (p - &1)) <=
         sum s (\i. w i * abs(x i) rpow q) /
         sum s (\i. w i * abs(x i) rpow (q - &1))`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN
     `!i:A. i IN s
            ==> w i * abs((x:A->real) i) rpow (p - &1) * abs(x i) =
                w i * abs(x i) rpow p /\
                w i * abs(x i) rpow (p - &1) * abs(x i) rpow (q - p) =
                w i * abs(x i) rpow (q - &1) /\
                w i * abs(x i) rpow (p - &1) * abs(x i) *
                abs(x i) rpow (q - p) =
                w i * abs(x i) rpow q`
     ASSUME_TAC THENL
    [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
     ASM_CASES_TAC `(w:A->real) i = &0` THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
     SUBGOAL_THEN
       `abs((x:A->real) i) rpow (p - &1) * abs(x i) = abs(x i) rpow p /\
        abs(x i) rpow (p - &1) * abs(x i) rpow (q - p) =
        abs(x i) rpow (q - &1) /\
        abs(x i) rpow (p - &1) * abs(x i) * abs(x i) rpow (q - p) =
        abs(x i) rpow q`
       (fun th -> REWRITE_TAC[GSYM th; REAL_MUL_ASSOC]) THEN
     MATCH_MP_TAC RPOW_LEHMER_TERMS THEN
     ASM_REWRITE_TAC[REAL_ABS_POS; REAL_ABS_ZERO] THEN DISCH_TAC THEN
     REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[REAL_LT_LE];
     ALL_TAC]) THEN
  MP_TAC(ISPECL[`s:A->bool`;
                `\i:A. (w:A->real) i * abs((x:A->real) i) rpow (p - &1)`;
                `\i:A. abs((x:A->real) i)`; `(q:real) - p`]
           SUM_MUL_RPOW_SIMILARLY_LE) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS; REAL_SUB_LE;
               GSYM REAL_MUL_ASSOC] THEN
  (SUBGOAL_THEN
     `sum s (\i:A. w i * abs((x:A->real) i) rpow (p - &1) * abs(x i)) =
      sum s (\i. w i * abs(x i) rpow p) /\
      sum s (\i:A. w i * abs((x:A->real) i) rpow (p - &1) *
                   abs(x i) rpow (q - p)) =
      sum s (\i. w i * abs(x i) rpow (q - &1)) /\
      sum s (\i:A. w i * abs((x:A->real) i) rpow (p - &1) * abs(x i) *
                   abs(x i) rpow (q - p)) =
      sum s (\i. w i * abs(x i) rpow q)`
     (fun th -> REWRITE_TAC[th]) THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
     ALL_TAC]) THEN
  ABBREV_TAC `Np = sum s (\i:A. w i * abs((x:A->real) i) rpow p)` THEN
  ABBREV_TAC `Dp = sum s (\i:A. w i * abs((x:A->real) i) rpow (p - &1))` THEN
  ABBREV_TAC `Nq = sum s (\i:A. w i * abs((x:A->real) i) rpow q)` THEN
  ABBREV_TAC `Dq = sum s (\i:A. w i * abs((x:A->real) i) rpow (q - &1))` THEN
  (SUBGOAL_THEN `&0 <= Np /\ &0 <= Dp /\ &0 <= Nq /\ &0 <= Dq`
     STRIP_ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC["Np"; "Dp"; "Nq"; "Dq"] THEN REPEAT CONJ_TAC THEN
     MATCH_MP_TAC SUM_POS_LE THEN
     ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS];
     ALL_TAC]) THEN
  (DISCH_TAC THEN ASM_CASES_TAC `Dp = &0` THENL
    [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ];
     ALL_TAC]) THEN
  (ASM_CASES_TAC `Dq = &0` THENL
    [ALL_TAC;
     SUBGOAL_THEN `&0 < Dp /\ &0 < Dq` STRIP_ASSUME_TAC THENL
      [ASM_REWRITE_TAC[REAL_LT_LE];
       ALL_TAC] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
     REWRITE_TAC[REAL_FIELD `(a:real) / b * c = (c * a) / b`] THEN
     ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]) THEN
  SUBGOAL_THEN `Np = &0` (fun th -> ASM_REWRITE_TAC[th; real_div;
      REAL_MUL_LZERO; REAL_INV_0; REAL_MUL_RZERO; REAL_LE_REFL]) THEN
  (SUBGOAL_THEN `!i:A. i IN s ==> w i * abs((x:A->real) i) rpow (q - &1) = &0`
     ASSUME_TAC THENL
    [MATCH_MP_TAC SUM_POS_EQ_0 THEN
     ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_ABS_POS];
     ALL_TAC]) THEN EXPAND_TAC "Np" THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `(w:A->real) i = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ENTIRE] THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
   ASM_CASES_TAC `abs((x:A->real) i) = &0` THENL
    [ALL_TAC;
     SUBGOAL_THEN `&0 < abs((x:A->real) i)` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ASM_SIMP_TAC[REAL_LT_IMP_NZ; RPOW_POS_LT]]]) THEN
  ASM_REWRITE_TAC[RPOW_ZERO] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(MP_TAC o SPEC `i:A`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_ZERO]) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_LE]);;

(* ------------------------------------------------------------------------- *)
(* Carleman: sum_k (|a_1| ... |a_k|)^(1/k) <= e sum_k |a_k| for all real a_i *)
(* and all n. With c_i = (i+1)^i / i^(i-1), c_1 ... c_k = (k+1)^k, so AM-GM  *)
(* bounds the k-th term by sum_(i<=k) |a_i| c_i / (k(k+1)), and c_i / i = (1 *)
(* + 1/i)^i <= e.                                                            *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_CARLEMAN_WEIGHTS = prove
 (`!k. product (1..k) (\i. &(i + 1) pow i / &i pow (i - 1)) = &(k + 1) pow k`,
  INDUCT_TAC THEN
  REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(k + 1) - 1 = k`] THEN
  (SUBGOAL_THEN `~(&(k + 1) pow k = &0)` MP_TAC THENL
    [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN ARITH_TAC;
     ALL_TAC] THEN CONV_TAC REAL_FIELD));;

let CARLEMAN_WEIGHT_LE_E = prove
 (`!i. 1 <= i ==> (&(i + 1) pow i / &i pow (i - 1)) / &i <= exp(&1)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC o GEN_REWRITE_RULE
               I[LE_EXISTS]) THEN
  (REWRITE_TAC[ARITH_RULE `(1 + n) - 1 = n`; GSYM REAL_OF_NUM_ADD] THEN
   ABBREV_TAC `(t:real) = &1 + &n` THEN SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
    [EXPAND_TAC "t" THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN
     `((t:real) + &1) pow (1 + n) / t pow n / t = (&1 + inv t) pow (1 + n)`
     SUBST1_TAC THENL
    [SUBGOAL_THEN `&1 + inv (t:real) = (t + &1) / t` SUBST1_TAC THENL
      [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
       ALL_TAC] THEN REWRITE_TAC[REAL_POW_DIV; REAL_POW_ADD; REAL_POW_1] THEN
     SUBGOAL_THEN `~((t:real) pow n = &0)` MP_TAC THENL
      [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ];
       ALL_TAC] THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
     ALL_TAC]) THEN
  (TRANS_TAC REAL_LE_TRANS `exp(inv t) pow (1 + n)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
     MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
     ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
     ALL_TAC]) THEN REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_OF_NUM_ADD] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]);;

let SUM_PARTIAL_SUMS_DIV_CONSECUTIVE = prove
 (`!b n. sum (1..n) (\k. sum (1..k) b / (&k * (&k + &1))) =
       sum (1..n) (\i. b i * (inv(&i) - inv(&n + &1)))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
  (ASM_REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
   REWRITE_TAC[SUM_SUB_NUMSEG; SUM_RMUL; GSYM REAL_OF_NUM_SUC] THEN
   REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`;
               GSYM REAL_OF_NUM_SUC] THEN SUBGOAL_THEN `&0 <= &n` MP_TAC THENL
    [REWRITE_TAC[REAL_POS];
     ALL_TAC] THEN CONV_TAC REAL_FIELD));;

let CARLEMAN_TERM_LE = prove
 (`!a k. 1 <= k
       ==> product (1..k) (\i. abs(a i)) rpow (&1 / &k) <=
           sum (1..k) (\i. abs(a i) * (&(i + 1) pow i / &i pow (i - 1))) /
           (&k * (&k + &1))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (SUBGOAL_THEN `!i. 1 <= i ==> &0 < &(i + 1) pow i / &i pow (i - 1)`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN
     MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
     ASM_ARITH_TAC;
     ALL_TAC]) THEN
  (MP_TAC(ISPECL[`1..k`;
                 `\i. abs((a:num->real) i) *
                      (&(i + 1) pow i / &i pow (i - 1))`;
                 `k:num`] AGM_RPOW) THEN
   REWRITE_TAC[HAS_SIZE_NUMSEG_1; IN_NUMSEG] THEN ANTS_TAC THENL
    [CONJ_TAC THENL
      [ASM_ARITH_TAC;
       REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE]];
     ALL_TAC]) THEN
  SIMP_TAC[GSYM RPOW_PRODUCT; FINITE_NUMSEG; PRODUCT_MUL; RPOW_MUL;
           PRODUCT_CARLEMAN_WEIGHTS; real_div; SUM_RMUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM RPOW_POW] THEN
  SIMP_TAC[RPOW_RPOW; REAL_POS; REAL_ARITH `&0 <= &k + &1`] THEN
  ASM_SIMP_TAC[REAL_MUL_LID; REAL_MUL_RINV; REAL_LT_IMP_NZ; RPOW_POW;
               REAL_POW_1] THEN DISCH_TAC THEN POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] (prove(
      `!G S k. &0 < k /\ G * (k + &1) <= S * inv k
               ==> G <= S * inv(k * (k + &1))`,
        REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM real_div]) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
                   REAL_ARITH `&0 < k ==> &0 < k + &1`]))) THEN
  ASM_REWRITE_TAC[]);;

let CARLEMAN_INEQUALITY = prove
 (`!a n. sum (1..n) (\k. product (1..k) (\i. abs(a i)) rpow (&1 / &k)) <=
       exp(&1) * sum (1..n) (\k. abs(a k))`,
  REPEAT GEN_TAC THEN
  (TRANS_TAC REAL_LE_TRANS
     `sum (1..n) (\k. sum (1..k) (\i. abs((a:num->real) i) *
                                      (&(i + 1) pow i / &i pow (i - 1)))
                      /
                      (&k * (&k + &1)))` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC SUM_LE_NUMSEG THEN SIMP_TAC[CARLEMAN_TERM_LE];
     ALL_TAC]) THEN REWRITE_TAC[SUM_PARTIAL_SUMS_DIV_CONSECUTIVE] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  (TRANS_TAC REAL_LE_TRANS `abs((a:num->real) i) * exp(&1)` THEN CONJ_TAC THENL
    [ALL_TAC;
     REAL_ARITH_TAC] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS]) THEN
  (TRANS_TAC REAL_LE_TRANS `(&(i + 1) pow i / &i pow (i - 1)) / &i` THEN
   ASM_SIMP_TAC[CARLEMAN_WEIGHT_LE_E] THEN
   GEN_REWRITE_TAC RAND_CONV[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
     ALL_TAC] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> b - c <= b`) THEN
   SIMP_TAC[REAL_LE_INV_EQ; REAL_ARITH `&0 <= &n ==> &0 <= &n + &1`;
            REAL_POS]));;

(* ------------------------------------------------------------------------- *)
(* Maclaurin-Newton. symmetric_mean s a k is S_k, the mean of the products   *)
(* of a over the k-subsets of the finite set s, with n = |s|. Newton,        *)
(* S_(k-1) S_(k+1) <= S_k^2 for all real a_i and every k >= 1 (S_j = 0 for   *)
(* j > n). For distinct a_i, by induction on n: the derivative of            *)
(* prod (x - a_i) has n - 1 distinct real roots b_j (Rolle) and the same     *)
(* means S_k for k < n; k = 1 is (sum a)^2 <= n sum a^2; k = n - 1 is        *)
(* trivial if some a_i = 0 (S_n = 0) and otherwise follows from k = 1 for    *)
(* 1/a_i. Repeated values follow by perturbing a by e c with c injective.    *)
(* Maclaurin, S_(k+1)^(1/(k+1)) <= S_k^(1/k), for a_i >= 0.                  *)
(* ------------------------------------------------------------------------- *)

let RESTRICTED_POWERSET_INSERT_SUC = prove
 (`!s:A->bool x k.
     ~(x IN s)
     ==> {t | t SUBSET (x INSERT s) /\ t HAS_SIZE (SUC k)} =
         {t | t SUBSET s /\ t HAS_SIZE (SUC k)} UNION
         IMAGE (\t. x INSERT t) {t | t SUBSET s /\ t HAS_SIZE k}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I[EXTENSION] THEN
  X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN u` THENL
     [DISJ2_TAC THEN EXISTS_TAC `u DELETE (x:A)` THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(u:A->bool) HAS_SIZE SUC k` THEN
      SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC(X_CHOOSE_THEN `t:A->bool`
          STRIP_ASSUME_TAC)) THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
      MAP_EVERY EXISTS_TAC[`x:A`; `t:A->bool`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]]]);;

let SUM_PRODUCT_SUBSETS_INSERT = prove
 (`!s:A->bool x a k.
     FINITE s /\ ~(x IN s)
     ==> sum {t | t SUBSET (x INSERT s) /\ t HAS_SIZE (SUC k)}
             (\t. product t a) =
         sum {t | t SUBSET s /\ t HAS_SIZE (SUC k)} (\t. product t a) +
         a x * sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RESTRICTED_POWERSET_INSERT_SUC] THEN
  (W(MP_TAC o PART_MATCH(lhand o rand) SUM_UNION o lhand o snd) THEN
   ANTS_TAC THENL
    [ASM_SIMP_TAC[FINITE_RESTRICTED_POWERSET; FINITE_IMAGE] THEN
     REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                 NOT_IN_EMPTY] THEN ASM SET_TAC[];
     DISCH_THEN SUBST1_TAC]) THEN
  (AP_TERM_TAC THEN
   W(MP_TAC o PART_MATCH(lhand o rand) SUM_IMAGE o lhand o snd) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
     DISCH_THEN SUBST1_TAC]) THEN REWRITE_TAC[GSYM SUM_LMUL; o_DEF] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN COND_CASES_TAC THEN ASM SET_TAC[]);;
let symmetric_mean = new_definition
 `symmetric_mean (s:A->bool) a k =
    sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a) /
    &(binom(CARD s,k))`;;

let SUM_PRODUCT_SUBSETS_SYMMETRIC_MEAN = prove
 (`!s:A->bool a k. FINITE s
     ==> sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a) =
         &(binom(CARD s,k)) * symmetric_mean s a k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[symmetric_mean] THEN
  ASM_CASES_TAC `binom(CARD(s:A->bool),k) = 0` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_FIELD `~((b:real) = &0) ==> e = b * e / b`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ]] THEN
  (MP_TAC(ISPECL[`CARD(s:A->bool)`; `k:num`; `s:A->bool`]
            HAS_SIZE_RESTRICTED_POWERSET) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[HAS_SIZE];
     ASM_REWRITE_TAC[HAS_SIZE_0] THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[SUM_CLAUSES; REAL_MUL_LZERO]]));;

let BINOM_SUC_SUC_STEPS = prove
 (`!n k. (n + 1) * binom(n,k + 1) = (n - k) * binom(n + 1,k + 1) /\
       (n + 1) * binom(n,k) = (k + 1) * binom(n + 1,k + 1)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL[`n:num`; `k + 1`] BINOM_TOP_STEP) THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) - (k + 1) = n - k`] THEN ARITH_TAC;
    ALL_TAC] THEN REWRITE_TAC[GSYM ADD1; binom] THEN
  MP_TAC(SPECL[`n:num`; `k:num`] BINOM_BOTTOM_STEP) THEN REWRITE_TAC[ADD1] THEN
  (REWRITE_TAC[LEFT_ADD_DISTRIB] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN ASM_CASES_TAC `(k:num) <= n` THENL
    [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
     SUBGOAL_THEN `binom(n,k) = 0` SUBST1_TAC THENL
      [REWRITE_TAC[BINOM_EQ_0] THEN ASM_ARITH_TAC;
       REWRITE_TAC[MULT_CLAUSES]]]));;

let SYMMETRIC_MEAN_INSERT = prove
 (`!s:A->bool x a k.
     FINITE s /\ ~(x IN s)
     ==> &(CARD s + 1) * symmetric_mean (x INSERT s) a (k + 1) =
         &(CARD s - k) * symmetric_mean s a (k + 1) +
         &(k + 1) * a x * symmetric_mean s a k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV) [symmetric_mean] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; GSYM ADD1; SUM_PRODUCT_SUBSETS_INSERT] THEN
  ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_SYMMETRIC_MEAN] THEN REWRITE_TAC[ADD1] THEN
  MP_TAC(SPECL[`CARD(s:A->bool)`; `k:num`] BINOM_SUC_SUC_STEPS) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_ADD] THEN
  (SUBGOAL_THEN
     `!j. binom(CARD(s:A->bool),j) = 0 ==> symmetric_mean s a j = &0`
     (fun th -> MP_TAC(SPEC `k:num` th) THEN MP_TAC(SPEC `k + 1` th)) THENL
    [SIMP_TAC[symmetric_mean; real_div; REAL_INV_0; REAL_MUL_RZERO];
     ALL_TAC]) THEN MP_TAC(SPEC `CARD(s:A->bool)` REAL_POS) THEN
  SPEC_TAC(`symmetric_mean (s:A->bool) a (k + 1)`, `s1:real`) THEN
  SPEC_TAC(`symmetric_mean (s:A->bool) a k`, `s0:real`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  SPEC_TAC(`&(binom (CARD(s:A->bool),k + 1))`, `c1:real`) THEN
  SPEC_TAC(`&(binom (CARD(s:A->bool),k))`, `c0:real`) THEN
  SPEC_TAC(`&(binom (CARD(s:A->bool) + 1,k + 1))`, `c:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  (ASM_CASES_TAC `c = &0` THENL
    [ALL_TAC;
     UNDISCH_TAC `~(c = &0)` THEN REPEAT(POP_ASSUM MP_TAC) THEN
     CONV_TAC REAL_FIELD]) THEN
  (SUBGOAL_THEN `(c1:real) = &0 /\ (c0:real) = &0` STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(fun th -> FIRST_X_ASSUM(MP_TAC o
          REWRITE_RULE[th; REAL_MUL_RZERO; REAL_ENTIRE])) THEN
     UNDISCH_TAC `&0 <= &(CARD(s:A->bool))` THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_SIMP_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;

let SYMMETRIC_MEAN_POS_LE = prove
 (`!s:A->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i) ==> &0 <= symmetric_mean s a k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[symmetric_mean] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE];
    ASM SET_TAC[]]);;

let SYMMETRIC_MEAN_ZERO_SUC = prove
 (`!s:A->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i) /\ symmetric_mean s a k = &0
     ==> symmetric_mean s a (k + 1) = &0`,
  REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `!t:A->bool. t SUBSET s /\ t HAS_SIZE k ==> product t a = &0`
     ASSUME_TAC THENL
    [MP_TAC(ISPECL[`\t:A->bool. product t a`;
                   `{t:A->bool | t SUBSET s /\ t HAS_SIZE k}`]
              SUM_POS_EQ_0) THEN
     ASM_SIMP_TAC[FINITE_RESTRICTED_POWERSET;
                  SUM_PRODUCT_SUBSETS_SYMMETRIC_MEAN; REAL_MUL_RZERO;
                  IN_ELIM_THM] THEN ANTS_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN CONJ_TAC THENL
        [ASM_MESON_TAC[HAS_SIZE];
         ASM SET_TAC[]];
       SIMP_TAC[]];
     ALL_TAC]) THEN REWRITE_TAC[symmetric_mean; real_div] THEN
  MATCH_MP_TAC(MESON[REAL_MUL_LZERO] `(x:real) = &0 ==> x * y = &0`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM ADD1; HAS_SIZE_CLAUSES] THEN
  X_GEN_TAC `u:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC(X_CHOOSE_THEN `y:A`
        (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `FINITE(v:A->bool)` ASSUME_TAC THENL
    [ASM_MESON_TAC[HAS_SIZE];
     ASM_SIMP_TAC[PRODUCT_CLAUSES; REAL_ENTIRE] THEN DISJ2_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]));;

let SYMMETRIC_MEAN_0 = prove
 (`!s:A->bool a. FINITE s ==> symmetric_mean s a 0 = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[symmetric_mean; binom; HAS_SIZE_0] THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ t = {}} = {{}}` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I[EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    GEN_TAC THEN EQ_TAC THEN SIMP_TAC[EMPTY_SUBSET];
    REWRITE_TAC[SUM_SING; PRODUCT_CLAUSES] THEN REAL_ARITH_TAC]);;

let SYMMETRIC_MEAN_EQ_0 = prove
 (`!s:A->bool a j. CARD s < j ==> symmetric_mean s a j = &0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[symmetric_mean; real_div] THEN
  SUBGOAL_THEN `binom(CARD(s:A->bool),j) = 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[BINOM_EQ_0];
    REWRITE_TAC[REAL_INV_0; REAL_MUL_RZERO]]);;

let HAS_REAL_DERIVATIVE_PRODUCT = prove
 (`!s:A->bool f f' x.
     FINITE s /\
     (!i. i IN s ==> ((\x. f i x) has_real_derivative f' i x) (atreal x))
     ==> ((\x. product s (\i. f i x)) has_real_derivative
          sum s (\i. f' i x * product (s DELETE i) (\j. f j x))) (atreal x)`,
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
   [`\x. (f:A->real->real) a x`; `(f':A->real->real) a x`;
    `\x. product s (\i. (f:A->real->real) i x)`;
    `sum s (\i. (f':A->real->real) i x * product (s DELETE i) (\j. f j x))`;
    `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[]);;

let SUM_PRODUCT_SUBSETS_0 = prove
 (`!s:A->bool b. sum {t | t SUBSET s /\ t HAS_SIZE 0} (\t. product t b) = &1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ t HAS_SIZE 0} = {{}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; HAS_SIZE_0] THEN
    MESON_TAC[EMPTY_SUBSET];
    REWRITE_TAC[SUM_SING; PRODUCT_CLAUSES]]);;

let SUM_SHIFT_SUC = prove
 (`!f m. sum(0..SUC m) f = f 0 + sum(0..m) (\i. f(SUC i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD1] THEN
  MP_TAC(ISPECL [`f:num->real`; `0`; `m + 1`] SUM_CLAUSES_LEFT) THEN
  REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`1`; `f:num->real`; `0`; `m:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let PRODUCT_ONE_ADD_MUL_SUBSETS = prove
 (`!s:A->bool b y n.
     FINITE s /\ CARD s <= n
     ==> product s (\j. &1 + y * b j) =
         sum(0..n)
           (\k. sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t b) *
                y pow k)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; PRODUCT_CLAUSES] THEN
    REWRITE_TAC[SUBSET_EMPTY; real_pow; REAL_MUL_RID] THEN
    SUBGOAL_THEN
     `!k. {t:A->bool | t = {} /\ t HAS_SIZE k} = if k = 0 then {{}} else {}`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `u:A->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; HAS_SIZE_0] THEN
      REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[CARD_CLAUSES];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SING; PRODUCT_CLAUSES] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &1 = &1 + x`) THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:A->real`; `y:real`; `n:num`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; PRODUCT_CLAUSES] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. n = SUC m /\ CARD(s:A->bool) <= m`
   (CHOOSE_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun ih ->
    MP_TAC(SPECL [`b:A->real`; `y:real`; `m:num`] ih) THEN
    MP_TAC(SPECL [`b:A->real`; `y:real`; `SUC m`] ih)) THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m <= SUC n`] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[SUM_SHIFT_SUC; SUM_PRODUCT_SUBSETS_0] THEN
  ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_INSERT; SUM_PRODUCT_SUBSETS_0] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG; real_pow] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `t = (y:real) * b * (&1 * &1 + v)
    ==> &1 * (&1 * &1 + v) + (y * b) * (&1 * &1 + v) = &1 * &1 + v + t`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_AC]);;

let SUM_PRODUCT_SUBSETS_DELETE = prove
 (`!s:A->bool a k.
     FINITE s
     ==> sum s (\i. sum {t | t SUBSET (s DELETE i) /\ t HAS_SIZE k}
                        (\t. product t a)) =
         &(CARD s - k) *
         sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. {t | t SUBSET (s DELETE i) /\ t HAS_SIZE k} =
        {t | t IN {t | t SUBSET s /\ t HAS_SIZE k} /\ ~((i:A) IN t)}`
   (fun th -> REWRITE_TAC[th; SUM_RESTRICT_SET]) THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_RESTRICTED_SUBSETS] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `t:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{i:A | i IN s /\ ~(i IN t)} = s DIFF t` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_DIFF; CARD_DIFF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[]);;

let PRODUCT_SUB_SUM_SUBSETS = prove
 (`!s:A->bool b x.
     FINITE s
     ==> product s (\j. x - b j) =
         sum(0..CARD s)
           (\k. --(&1) pow k *
                sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t b) *
                x pow (CARD s - k))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_SUB_LZERO] THEN
    ASM_SIMP_TAC[PRODUCT_NEG] THEN
    SUBGOAL_THEN
     `sum(0..CARD(s:A->bool))
        (\k. --(&1) pow k *
             sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t b) *
             &0 pow (CARD s - k)) =
      sum(0..CARD s)
        (\k. if k = CARD s
             then --(&1) pow CARD s *
                  sum {t | t SUBSET s /\ t HAS_SIZE CARD s} (\t. product t b)
             else &0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_POW_ZERO] THEN
      ASM_CASES_TAC `k = CARD(s:A->bool)` THEN
      ASM_REWRITE_TAC[SUB_REFL; REAL_MUL_RID] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[REAL_MUL_RZERO]];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ t HAS_SIZE CARD s} = {s}`
     (fun th -> REWRITE_TAC[th; SUM_SING]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; HAS_SIZE] THEN
    ASM_MESON_TAC[CARD_SUBSET_EQ; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product s (\j. x - (b:A->real) j) =
    product s (\j. x * (&1 + --inv x * b j))` SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST] THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->real`; `--inv(x:real)`;
                 `CARD(s:A->bool)`] PRODUCT_ONE_ADD_MUL_SUBSETS) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_POW_NEG; REAL_POW_INV] THEN
  REWRITE_TAC[REAL_POW_ONE] THEN COND_CASES_TAC THEN
  REWRITE_TAC[real_div] THEN
  REWRITE_TAC[REAL_MUL_AC; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_MUL_LID]);;

let SUM_PRODUCT_DELETE_SUB = prove
 (`!s:A->bool a x.
     FINITE s
     ==> sum s (\i. product (s DELETE i) (\j. x - a j)) =
         sum(0..CARD s - 1)
           (\k. --(&1) pow k * &(CARD s - k) *
                sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a) *
                x pow (CARD s - 1 - k))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum s (\i. sum(0..CARD(s:A->bool) - 1)
       (\k. --(&1) pow k *
            sum {t | t SUBSET (s DELETE i) /\ t HAS_SIZE k} (\t. product t a) *
            x pow (CARD s - 1 - k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[PRODUCT_SUB_SUM_SUBSETS; FINITE_DELETE; CARD_DELETE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(c:real) * e * p = (c * p) * e`; SUM_LMUL] THEN
  ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_DELETE] THEN REWRITE_TAC[REAL_MUL_AC] THEN
  REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_DELETE] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let SUM_PRODUCT_DELETE_SUB_ROOT = prove
 (`!s:A->bool a u.
     FINITE s /\ u IN s /\ (?v. v IN s /\ a u < a v)
     ==> ?z. a u < z /\ (!v. v IN s /\ a u < a v ==> z < a v) /\
             sum s (\i. product (s DELETE i) (\j. z - a j)) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (a:A->real) {w | w IN s /\ a u < a w}` INF_FINITE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = inf (IMAGE (a:A->real) {w | w IN s /\ a u < a w})` THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. ((\x. product s (\j. x - (a:A->real) j)) has_real_derivative
         sum s (\i. product (s DELETE i) (\j. x - a j))) (atreal x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:A->bool`; `\j:A x:real. x - (a:A->real) j`;
                   `\j:A x:real. &1`; `x:real`]
           HAS_REAL_DERIVATIVE_PRODUCT) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real. x`; `&1`; `\x:real. (a:A->real) i`; `&0`;
                   `atreal x`] HAS_REAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST;
                REAL_SUB_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. product s (\j. x - (a:A->real) j)`;
    `\x. sum s (\i. product (s DELETE i) (\j. x - (a:A->real) j))`;
    `(a:A->real) u`; `c:real`] REAL_ROLLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = &0 /\ y = &0 ==> x = y`) THEN
      ASM_SIMP_TAC[PRODUCT_EQ_0] THEN CONJ_TAC THENL
       [EXISTS_TAC `u:A`; EXISTS_TAC `w:A`] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL];
      MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[real_differentiable_on; real_differentiable] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC
       `sum s (\i. product (s DELETE i) (\j. x - (a:A->real) j))` THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_POLYFUN_DISTINCT_ROOTS_EQ_0 = prove
 (`!N d (t:A->bool) b.
     FINITE t /\ CARD t = N /\
     (!i j. i IN t /\ j IN t /\ b i = b j ==> i = j) /\ d 0 = &0 /\
     (!i. i IN t ==> sum(0..N) (\k. d k * b i pow (N - k)) = &0)
     ==> !k. k <= N ==> d k = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `N = 0` THENL
   [ASM_SIMP_TAC[LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?M. N = SUC M` (X_CHOOSE_THEN `M:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `N - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. sum(0..SUC M) (\k. d k * x pow (SUC M - k)) =
        sum(0..M) (\i. d(SUC M - i) * x pow i)`
  ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
    REWRITE_TAC[LT; SUB_0; SUM_CLAUSES_NUMSEG; LE_0; SUB_REFL] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN 0..M ==> d(SUC M - i) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`M:num`; `\i. (d:num->real)(SUC M - i)`]
           REAL_POLYFUN_ROOTBOUND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `CARD(IMAGE (b:A->real) t) = SUC M` ASSUME_TAC THENL
     [ASM_MESON_TAC[CARD_IMAGE_INJ]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (b:A->real) t`;
      `{x | sum(0..M) (\i. (d:num->real)(SUC M - i) * x pow i) = &0}`]
     CARD_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                              is_eq(snd(dest_forall(concl th)))
                           then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      ASM_SIMP_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC M - k`) THEN
  REWRITE_TAC[IN_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `k <= SUC M /\ ~(k = 0) ==> SUC M - (SUC M - k) = k`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let SYMMETRIC_MEAN_DELETE_EXISTS = prove
 (`!s:A->bool a.
     FINITE s /\ 2 <= CARD s /\
     (!i j. i IN s /\ j IN s /\ a i = a j ==> i = j)
     ==> ?m b. m IN s /\
               (!i j. i IN s DELETE m /\ j IN s DELETE m /\ b i = b j
                      ==> i = j) /\
               (!k. k < CARD s
                    ==> symmetric_mean (s DELETE m) b k =
                        symmetric_mean s a k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (a:A->real) s` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `2 <= CARD(s:A->bool)` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `!x. x IN s ==> (a:A->real) x <= sup (IMAGE a s)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u. ?z. u IN s DELETE m
            ==> (a:A->real) u < z /\ (!v. v IN s /\ a u < a v ==> z < a v) /\
                sum s (\i. product (s DELETE i) (\j. z - a j)) = &0`
  MP_TAC THENL
   [X_GEN_TAC `u:A` THEN REWRITE_TAC[IN_DELETE; RIGHT_EXISTS_IMP_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUM_PRODUCT_DELETE_SUB_ROOT THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:A` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:A->real`) THEN EXISTS_TAC `b:A->real` THEN
  SUBGOAL_THEN
   `!i j. i IN s DELETE m /\ j IN s DELETE m /\ (b:A->real) i = b j ==> i = j`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:A = j` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((a:A->real) i = a j)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
    MP_TAC(SPECL [`(a:A->real) i`; `(a:A->real) j`] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_MESON_TAC[IN_DELETE; REAL_LT_TRANS; REAL_LT_REFL];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL
   [`CARD(s:A->bool) - 1`;
    `\k. --(&1) pow k *
         (&(CARD(s:A->bool) - k) *
          sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t (a:A->real)) -
          &(CARD s) *
          sum {t | t SUBSET (s DELETE m) /\ t HAS_SIZE k}
              (\t. product t (b:A->real)))`;
    `s DELETE (m:A)`; `b:A->real`] REAL_POLYFUN_DISTINCT_ROOTS_EQ_0) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; SUM_PRODUCT_SUBSETS_0] THEN
  REWRITE_TAC[real_pow; SUB_0; REAL_MUL_LID; REAL_MUL_RID; REAL_SUB_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS
     `sum(0..CARD(s:A->bool) - 1)
        (\k. --(&1) pow k * &(CARD s - k) *
             sum {t | t SUBSET s /\ t HAS_SIZE k}
                 (\t. product t (a:A->real)) *
             (b:A->real) i pow (CARD s - 1 - k)) -
      &(CARD s) *
      sum(0..CARD s - 1)
        (\k. --(&1) pow k *
             sum {t | t SUBSET (s DELETE m) /\ t HAS_SIZE k}
                 (\t. product t b) *
             b i pow (CARD s - 1 - k))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM SUM_LMUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM SUM_SUB_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC[REAL_MUL_AC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:A->bool`; `a:A->real`; `(b:A->real) i`]
           SUM_PRODUCT_DELETE_SUB) THEN
    MP_TAC(ISPECL [`s DELETE (m:A)`; `b:A->real`; `(b:A->real) i`]
           PRODUCT_SUB_SUM_SUBSETS) THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `product (s DELETE m) (\j. (b:A->real) i - b j) = &0`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0; FINITE_DELETE] THEN EXISTS_TAC `i:A` THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_NEG_EQ_0; REAL_OF_NUM_EQ;
              ARITH_EQ; REAL_SUB_0] THEN
  ASM_SIMP_TAC[symmetric_mean; CARD_DELETE] THEN
  MP_TAC(SPECL [`CARD(s:A->bool) - 1`; `k:num`] BINOM_TOP_STEP) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> n - 1 + 1 = n`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN
   `~(&(binom(CARD(s:A->bool),k)) = &0) /\
    ~(&(binom(CARD s - 1,k)) = &0) /\ ~(&(CARD s - k) = &0)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; BINOM_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`sum {t | t SUBSET (s DELETE m) /\ t HAS_SIZE k}
                (\t. product t (b:A->real))`, `eb:real`) THEN
  SPEC_TAC(`sum {t | t SUBSET s /\ t HAS_SIZE k}
                (\t. product t (a:A->real))`, `ea:real`) THEN
  SPEC_TAC(`&(binom(CARD(s:A->bool),k))`, `ca:real`) THEN
  SPEC_TAC(`&(binom(CARD(s:A->bool) - 1,k))`, `cb:real`) THEN
  SPEC_TAC(`&(CARD(s:A->bool) - k)`, `d:real`) THEN
  SPEC_TAC(`&(CARD(s:A->bool))`, `n:real`) THEN
  CONV_TAC REAL_FIELD);;

let REAL_BINOM_2 = prove
 (`!n. &(binom(n,2)) = &n * (&n - &1) / &2`,
  INDUCT_TAC THEN
  REWRITE_TAC[binom; ARITH_RULE `2 = SUC 1`; BINOM_1] THEN
  REWRITE_TAC[ARITH_RULE `SUC 1 = 2`; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_SUC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SUM_PRODUCT_SUBSETS_1 = prove
 (`!s:A->bool a.
     sum {t | t SUBSET s /\ t HAS_SIZE 1} (\t. product t a) = sum s a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ t HAS_SIZE 1} = IMAGE (\x. {x}) s`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; ONE; HAS_SIZE_CLAUSES; HAS_SIZE_0] THEN
    REWRITE_TAC[NOT_IN_EMPTY; UNWIND_THM2] THEN
    MESON_TAC[SING_SUBSET];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF; PRODUCT_SING; ETA_AX]);;

let SUM_PRODUCT_SUBSETS_2 = prove
 (`!s:A->bool a.
     FINITE s
     ==> &2 * sum {t | t SUBSET s /\ t HAS_SIZE 2} (\t. product t a) =
         sum s a pow 2 - sum s (\i. a i pow 2)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_EMPTY; SUM_CLAUSES] THEN
    SUBGOAL_THEN `{t:A->bool | t = {} /\ t HAS_SIZE 2} = {}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `u:A->bool` THEN ASM_CASES_TAC `u:A->bool = {}` THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THEN ARITH_TAC;
      REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC 1`] THEN
  ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_INSERT; SUM_CLAUSES;
               SUM_PRODUCT_SUBSETS_1] THEN
  REWRITE_TAC[ARITH_RULE `SUC 1 = 2`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  SPEC_TAC(`sum {t | t SUBSET s /\ t HAS_SIZE 2} (\t. product t (a:A->real))`,
           `e:real`) THEN
  SPEC_TAC(`sum s (\i. (a:A->real) i pow 2)`, `q:real`) THEN
  SPEC_TAC(`sum s (a:A->real)`, `p:real`) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let NEWTON_INEQUALITY_1 = prove
 (`!s:A->bool a.
     FINITE s
     ==> symmetric_mean s a 0 * symmetric_mean s a 2 <=
         symmetric_mean s a 1 pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_0; REAL_MUL_LID] THEN
  ASM_CASES_TAC `CARD(s:A->bool) < 2` THENL
   [ASM_SIMP_TAC[SYMMETRIC_MEAN_EQ_0; REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[symmetric_mean; SUM_PRODUCT_SUBSETS_1; BINOM_1;
               REAL_BINOM_2] THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->real`] SUM_PRODUCT_SUBSETS_2) THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->real`] SUM_POW_2_LE_CARD_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 <= &(CARD(s:A->bool))` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`sum {t | t SUBSET s /\ t HAS_SIZE 2} (\t. product t (a:A->real))`,
           `e:real`) THEN
  SPEC_TAC(`sum s (\i. (a:A->real) i pow 2)`, `q:real`) THEN
  SPEC_TAC(`sum s (a:A->real)`, `p:real`) THEN
  SPEC_TAC(`&(CARD(s:A->bool))`, `n:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  SUBGOAL_THEN
   `(p / n) pow 2 - e / (n * (n - &1) / &2) =
    (n * q - p pow 2) / (n pow 2 * (n - &1))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&2 * e = p pow 2 - q` THEN UNDISCH_TAC `&2 <= n` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC]]);;

let SYMMETRIC_MEAN_CARD = prove
 (`!s:A->bool b. FINITE s ==> symmetric_mean s b (CARD s) = product s b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[symmetric_mean; BINOM_REFL; REAL_DIV_1] THEN
  SUBGOAL_THEN `{t:A->bool | t SUBSET s /\ t HAS_SIZE CARD s} = {s}`
   (fun th -> REWRITE_TAC[th; SUM_SING]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING; HAS_SIZE] THEN
  ASM_MESON_TAC[CARD_SUBSET_EQ; SUBSET_REFL]);;

let SYMMETRIC_MEAN_INV = prove
 (`!s:A->bool a j.
     FINITE s /\ (!i. i IN s ==> ~(a i = &0)) /\ j <= CARD s
     ==> symmetric_mean s (\i. inv(a i)) j * symmetric_mean s a (CARD s) =
         symmetric_mean s a (CARD s - j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_CARD] THEN
  REWRITE_TAC[symmetric_mean] THEN
  ASM_SIMP_TAC[BINOM_SYM] THEN
  SUBGOAL_THEN
   `sum {t | t SUBSET s /\ t HAS_SIZE j}
        (\t. product t (\i. inv((a:A->real) i))) * product s a =
    sum {t | t SUBSET s /\ t HAS_SIZE (CARD s - j)} (\t. product t a)`
  MP_TAC THENL
   [ALL_TAC;
    SPEC_TAC(`sum {t | t SUBSET s /\ t HAS_SIZE (CARD s - j)}
                  (\t. product t (a:A->real))`, `e1:real`) THEN
    SPEC_TAC(`sum {t | t SUBSET s /\ t HAS_SIZE j}
                  (\t. product t (\i. inv((a:A->real) i)))`, `e0:real`) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[real_div; REAL_MUL_AC]] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  TRANS_TAC EQ_TRANS
   `sum {t | t SUBSET s /\ t HAS_SIZE j}
        (\t. product (s DIFF t) (a:A->real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(t:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:A->real`; `t:A->bool`; `s DIFF t:A->bool`]
           PRODUCT_UNION) THEN
    ASM_SIMP_TAC[FINITE_DIFF; SET_RULE `DISJOINT t (s DIFF t)`] THEN
    SUBGOAL_THEN `t UNION (s DIFF t):A->bool = s` SUBST1_TAC THENL
     [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN
    SUBGOAL_THEN `product t (\x. inv((a:A->real) x) * a x) = &1`
     (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t SUBSET s /\ t HAS_SIZE (CARD s - j)} =
    IMAGE (\t. s DIFF t) {t:A->bool | t SUBSET s /\ t HAS_SIZE j}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `s DIFF u:A->bool` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
      ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF] THEN
      REPEAT CONJ_TAC THEN FIRST [ASM_ARITH_TAC; ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
      ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF] THEN
      REPEAT CONJ_TAC THEN FIRST [ASM_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let NEWTON_INEQUALITY_INJ = prove
 (`!n s:A->bool a k.
     FINITE s /\ CARD s = n /\
     (!i j. i IN s /\ j IN s /\ a i = a j ==> i = j) /\ 1 <= k
     ==> symmetric_mean s a (k - 1) * symmetric_mean s a (k + 1) <=
         symmetric_mean s a k pow 2`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `a:A->real`; `k:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n < k + 1` THENL
   [SUBGOAL_THEN `symmetric_mean s (a:A->real) (k + 1) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SYMMETRIC_MEAN_EQ_0 THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2]];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[NEWTON_INEQUALITY_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `k + 2 <= n` THENL
   [MP_TAC(ISPECL [`s:A->bool`; `a:A->real`] SYMMETRIC_MEAN_DELETE_EXISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A` (X_CHOOSE_THEN `b:A->real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ih" (MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s DELETE (m:A)`; `b:A->real`; `k:num`]) THEN
    ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN
    SUBGOAL_THEN `k - 1 < n /\ k < n /\ k + 1 < n` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `3 <= CARD(s:A->bool)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k = CARD(s:A->bool) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> n - 1 - 1 = n - 2 /\ n - 1 + 1 = n`] THEN
  UNDISCH_TAC `CARD(s:A->bool) = n` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  ASM_CASES_TAC `?i. i IN s /\ (a:A->real) i = &0` THENL
   [ASM_SIMP_TAC[SYMMETRIC_MEAN_CARD] THEN
    SUBGOAL_THEN `product s (a:A->real) = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_POW_2];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM;
                              TAUT `~(p /\ q) <=> p ==> ~q`]) THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i. inv((a:A->real) i)`]
         NEWTON_INEQUALITY_1) THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->real`; `1`] SYMMETRIC_MEAN_INV) THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->real`; `2`] SYMMETRIC_MEAN_INV) THEN
  ASM_SIMP_TAC[SYMMETRIC_MEAN_0; REAL_MUL_LID;
               ARITH_RULE `3 <= n ==> 1 <= n /\ 2 <= n`] THEN
  SPEC_TAC(`symmetric_mean s (\i. inv((a:A->real) i)) 1`, `x1:real`) THEN
  SPEC_TAC(`symmetric_mean s (\i. inv((a:A->real) i)) 2`, `x2:real`) THEN
  SPEC_TAC(`symmetric_mean s (a:A->real) (CARD s)`, `p:real`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ARITH `((x:real) * p) * p = x * p pow 2`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

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

let SYMMETRIC_MEAN_REAL_CONTINUOUS = prove
 (`!s:A->bool a c k x.
     FINITE s
     ==> (\e. symmetric_mean s (\i. a i + e * c i) k) real_continuous
         atreal x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[symmetric_mean; real_div] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_SUM THEN
  ASM_SIMP_TAC[FINITE_RESTRICTED_SUBSETS; IN_ELIM_THM] THEN
  X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_PRODUCT THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_ID]);;

let NEWTON_INEQUALITY = prove
 (`!s:A->bool a k.
     FINITE s /\ 1 <= k
     ==> symmetric_mean s a (k - 1) * symmetric_mean s a (k + 1) <=
         symmetric_mean s a k pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:num->A`; `1..CARD(s:A->bool)`]
         INJECTIVE_ON_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:A->num`) THEN
  ABBREV_TAC `c = \z. &((g:A->num) z)` THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s /\ (c:A->real) x = c y ==> x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `s = IMAGE (f:num->A) (1..CARD s)` THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(ISPECL
   [`\e. symmetric_mean s (\i. (a:A->real) i + e * (c:A->real) i) k pow 2 -
         symmetric_mean s (\i. a i + e * c i) (k - 1) *
         symmetric_mean s (\i. a i + e * c i) (k + 1)`;
    `&0`;
    `{((a:A->real) j - a i) / ((c:A->real) i - c j) | i IN s /\ j IN s}`]
   REAL_CONTINUOUS_NONNEG_COFINITE) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_POW;
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC] THEN
    ASM_SIMP_TAC[SYMMETRIC_MEAN_REAL_CONTINUOUS];
    MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  MATCH_MP_TAC NEWTON_INEQUALITY_INJ THEN EXISTS_TAC `CARD(s:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:A = j` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((c:A->real) i = c j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `j:A`] o
    check (fun th -> is_forall(concl th) &&
                     not(is_imp(snd(strip_forall(concl th)))))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(a:A->real) i + e * c i = a j + e * c j` THEN
  UNDISCH_TAC `~((c:A->real) i = c j)` THEN CONV_TAC REAL_FIELD);;

let SYMMETRIC_MEAN_POW_MONO = prove
 (`!s:A->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i)
     ==> symmetric_mean s a (k + 1) pow k <= symmetric_mean s a k pow (k + 1)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THENL
   [ASM_SIMP_TAC[real_pow; ADD_CLAUSES; SYMMETRIC_MEAN_0; REAL_POW_1;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  (REWRITE_TAC[ADD1] THEN
   ASM_CASES_TAC `symmetric_mean (s:A->bool) a (k + 1) = &0` THENL
    [SUBGOAL_THEN `symmetric_mean (s:A->bool) a ((k + 1) + 1) = &0`
       SUBST1_TAC THENL
      [MATCH_MP_TAC SYMMETRIC_MEAN_ZERO_SUC THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[REAL_POW_ZERO; ADD_EQ_0; ARITH_EQ; REAL_LE_REFL]];
     ALL_TAC]) THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->real`; `k + 1`] NEWTON_INEQUALITY) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= k + 1 /\ (k + 1) - 1 = k`] THEN
  MP_TAC(ISPECL[`s:A->bool`; `a:A->real`] SYMMETRIC_MEAN_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `k:num` th) THEN
             MP_TAC(SPEC `k + 1` th) THEN MP_TAC(SPEC `(k + 1) + 1` th)) THEN
  UNDISCH_TAC
    `symmetric_mean (s:A->bool) a (k + 1) pow k
     <= symmetric_mean s a k pow (k + 1)` THEN
  UNDISCH_TAC `~(symmetric_mean (s:A->bool) a (k + 1) = &0)` THEN
  SPEC_TAC(`symmetric_mean (s:A->bool) a ((k + 1) + 1)`, `D:real`) THEN
  SPEC_TAC(`symmetric_mean (s:A->bool) a (k + 1)`, `C:real`) THEN
  SPEC_TAC(`symmetric_mean (s:A->bool) a k`, `B:real`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  (SUBGOAL_THEN `&0 < C pow k` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ
        th)]) THEN
  (TRANS_TAC REAL_LE_TRANS `(B:real) pow (k + 1) * D pow (k + 1)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE];
     ALL_TAC]) THEN
  (REWRITE_TAC[GSYM REAL_POW_MUL] THEN
   TRANS_TAC REAL_LE_TRANS `((C:real) pow 2) pow (k + 1)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL];
     REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_POW] THEN
     MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN ARITH_TAC]));;

let MACLAURIN_INEQUALITY = prove
 (`!s:A->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i) /\ 1 <= k
     ==> symmetric_mean s a (k + 1) rpow (&1 / &(k + 1)) <=
         symmetric_mean s a k rpow (&1 / &k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
  EXISTS_TAC `k * (k + 1)` THEN
  ASM_SIMP_TAC[RPOW_POS_LE; SYMMETRIC_MEAN_POS_LE; MULT_EQ_0;
               ARITH_RULE `1 <= k ==> ~(k = 0) /\ ~(k + 1 = 0)`] THEN
  (ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW; SYMMETRIC_MEAN_POS_LE;
                GSYM REAL_OF_NUM_MUL] THEN
   SUBGOAL_THEN `&0 < &k /\ &0 < &k + &1` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD]) THEN
  (SUBGOAL_THEN
     `&1 / (&k + &1) * &k * (&k + &1) = &k /\
      &1 / &k * &k * (&k + &1) = &k + &1`
     (fun th -> REWRITE_TAC[th]) THENL
    [UNDISCH_TAC `&0 < &k + &1` THEN UNDISCH_TAC `&0 < &k` THEN
     CONV_TAC REAL_FIELD;
     ALL_TAC]) THEN REWRITE_TAC[REAL_OF_NUM_ADD; RPOW_POW] THEN
  ASM_SIMP_TAC[SYMMETRIC_MEAN_POW_MONO]);;
