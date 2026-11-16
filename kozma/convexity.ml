(* ========================================================================= *)
(* Convexity, majorization and integral inequalities, from L. Kozma, "Useful *)
(* Inequalities" (v0.44).                                                    *)
(* ========================================================================= *)

needs "Library/permutations.ml";;
needs "Multivariate/realanalysis.ml";;
needs "kozma/real_lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* Jensen's inequality for concave f, and the chord-slope bounds f'(a) <=    *)
(* (f(b) - f(a))/(b - a) <= f'(b) for convex f.                              *)
(* ------------------------------------------------------------------------- *)

let REAL_CONCAVE_ON_IMP_JENSEN = prove
 (`!f s (k:A->bool) u x.
     (\t. --f t) real_convex_on s /\ is_realinterval s /\ FINITE k /\
     (!i. i IN k ==> &0 <= u i /\ x i IN s) /\ sum k u = &1
     ==> sum k (\i. u i * f(x i)) <= f(sum k (\i. u i * x i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real. --(f:real->real) t`; `s:real->bool`; `k:A->bool`;
                 `u:A->real`; `x:A->real`] REAL_CONVEX_ON_IMP_JENSEN) THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_LE_NEG2]);;

let CAUCHY_CONVEX_INEQUALITY = prove
 (`!f f'a f'b a b.
     a < b /\ f real_convex_on real_interval[a,b] /\
     (f has_real_derivative f'a) (atreal a within real_interval[a,b]) /\
     (f has_real_derivative f'b) (atreal b within real_interval[a,b])
     ==> f'a <= (f b - f a) / (b - a) /\ (f b - f a) / (b - a) <= f'b`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_SUB_LT] THENL
   [MATCH_MP_TAC REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP;
    MATCH_MP_TAC REAL_CONVEX_ON_SECANT_DERIVATIVE_IMP] THEN
  EXISTS_TAC `real_interval[a:real,b]` THEN
  ASM_SIMP_TAC[REAL_SEGMENT_INTERVAL; REAL_LT_IMP_LE; SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Gibbs' inequality: sum a_i phi(b_i/a_i) <= A phi(B/A) for concave phi,    *)
(* and the log-sum inequality A log(A/B) <= sum a_i log(a_i/b_i).            *)
(* ------------------------------------------------------------------------- *)

let GIBBS_INEQUALITY_GEN = prove
 (`!phi s (k:A->bool) a b.
     (\t. --phi t) real_convex_on s /\ is_realinterval s /\ FINITE k /\
     (!i. i IN k
          ==> &0 <= a i /\ (a i = &0 ==> b i = &0) /\
              (&0 < a i ==> b i / a i IN s))
     ==> sum k (\i. a i * phi(b i / a i)) <= sum k a * phi(sum k b / sum k a)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `sum k (a:A->real) = &0` THENL
   [SUBGOAL_THEN `!i. i IN k ==> (a:A->real) i = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sum k (a:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE; SUM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum k (\i. (a:A->real) i * phi((b:A->real) i / a i)) =
    sum k a *
    sum {i | i IN k /\ &0 < a i} (\i. a i / sum k a * phi(b i / a i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_RESTRICT_SET; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `~(sum k (a:A->real) = &0)` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `(a:A->real) i = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[REAL_LT_LE]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum k (b:A->real) / sum k a =
    sum {i | i IN k /\ &0 < (a:A->real) i} (\i. a i / sum k a * (b i / a i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_RESTRICT_SET; real_div; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [UNDISCH_TAC `&0 < (a:A->real) i` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `(b:A->real) i = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[REAL_LT_LE]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`phi:real->real`; `s:real->bool`;
                 `{i | i IN k /\ &0 < (a:A->real) i}`;
                 `\i. (a:A->real) i / sum k a`; `\i. (b:A->real) i / a i`]
                REAL_CONCAVE_ON_IMP_JENSEN) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  TRANS_TAC EQ_TRANS `sum k (\i. (a:A->real) i / sum k a)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:A->real) i = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[REAL_LT_LE]; REAL_ARITH_TAC];
    REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_SIMP_TAC[REAL_MUL_RINV]]);;

let GIBBS_INEQUALITY = prove
 (`!(k:A->bool) a b.
     FINITE k /\
     (!i. i IN k ==> &0 <= a i /\ &0 <= b i /\ (b i = &0 ==> a i = &0))
     ==> sum k a * log(sum k a / sum k b) <= sum k (\i. a i * log(a i / b i))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `sum k (a:A->real) = &0` THENL
   [SUBGOAL_THEN `!i. i IN k ==> (a:A->real) i = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_0 THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. j IN k /\ &0 < (a:A->real) j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUM_EQ_0; REAL_LT_LE]; ALL_TAC] THEN
  ABBREV_TAC `kk = {i | i IN k /\ &0 < (a:A->real) i}` THEN
  SUBGOAL_THEN
   `FINITE (kk:A->bool) /\ (j:A) IN kk /\
    (!i. i IN kk <=> i IN k /\ &0 < (a:A->real) i)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kk:A->bool) SUBSET k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN k /\ ~((i:A) IN kk) ==> (a:A->real) i = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (a:A->real) i /\ ~(&0 < a i)` MP_TAC THENL
     [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum k (a:A->real) = sum kk a /\
    sum k (\i. a i * log(a i / (b:A->real) i)) =
    sum kk (\i. a i * log(a i / b i))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN X_GEN_TAC `i:A` THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(fun h ->
      REWRITE_TAC[MATCH_MP h th; REAL_MUL_LZERO]));
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN kk ==> &0 < (a:A->real) i /\ &0 < (b:A->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 < (a:A->real) i /\ &0 <= (b:A->real) i /\ (b i = &0 ==> a i = &0)`
    MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sum kk (a:A->real) /\ &0 < sum kk (b:A->real) /\ sum kk b <= sum k b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LT THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUM_POS_LT THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[IN_DIFF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`log`; `{t:real | &0 < t}`; `kk:A->bool`; `a:A->real`;
                 `b:A->real`] GIBBS_INEQUALITY_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_CONVEX_ON_LOG; SUBSET_REFL; IN_ELIM_THM; REAL_LT_DIV;
                 REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum kk (\i. (a:A->real) i * log(a i / (b:A->real) i)) =
    --sum kk (\i. a i * log(b i / a i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(i:A) IN kk`)) THEN
    SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sum k (b:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN
  MP_TAC(ISPECL [`sum kk (b:A->real)`; `sum k (b:A->real)`]
                LOG_MONO_LE_IMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sum kk (a:A->real)`; `log(sum kk (b:A->real))`;
                 `log(sum k (b:A->real))`] REAL_LE_LMUL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Schur's inequality in Vornicu's form: f(x)(x-y)^k(x-z)^k + ... >= 0 for   *)
(* f >= 0 convex or monotone; the general form for x >= y >= z with          *)
(* f(y) <= f(x) or f(y) <= f(z).                                             *)
(* ------------------------------------------------------------------------- *)

let SCHUR_VORNICU_INEQUALITY_GEN = prove
 (`!f x y z k.
     z <= y /\ y <= x /\ &0 <= f x /\ &0 <= f y /\ &0 <= f z /\
     (f y <= f x \/ f y <= f z)
     ==> &0 <= f x * (x - y) pow k * (x - z) pow k +
               f y * (y - z) pow k * (y - x) pow k +
               f z * (z - x) pow k * (z - y) pow k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(y:real) - x = --(x - y) /\ (z:real) - x = --((x - y) + (y - z)) /\
    z - y = --(y - z) /\ x - z = (x - y) + (y - z)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (x:real) - y /\ &0 <= (y:real) - z` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`(x:real) - y`,`p:real`) THEN SPEC_TAC(`(y:real) - z`,`q:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= (p:real) pow k /\ &0 <= (q:real) pow k /\
    p pow k <= (p + q) pow k /\ q pow k <= (p + q) pow k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((p:real) + q) pow k` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (f:real->real) x * (p:real) pow k * (p + q) pow k /\
    &0 <= (f:real->real) z * ((p:real) + q) pow k * q pow k /\
    &0 <= (f:real->real) y * (q:real) pow k * p pow k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_NEG] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`(f:real->real) y`; `(f:real->real) x`; `(q:real) pow k`;
                  `((p:real) + q) pow k`] REAL_LE_MUL2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(f:real->real) y * (q:real) pow k`;
                  `(f:real->real) x * ((p:real) + q) pow k`;
                  `(p:real) pow k`] REAL_LE_RMUL);
    MP_TAC(SPECL [`(f:real->real) y`; `(f:real->real) z`; `(p:real) pow k`;
                  `((p:real) + q) pow k`] REAL_LE_MUL2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(f:real->real) y * (p:real) pow k`;
                  `(f:real->real) z * ((p:real) + q) pow k`;
                  `(q:real) pow k`] REAL_LE_RMUL)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHUR_VORNICU_INEQUALITY = prove
 (`!f s x y z k.
     x IN s /\ y IN s /\ z IN s /\ (!t. t IN s ==> &0 <= f t) /\
     (f real_convex_on s \/
      (!u v. u IN s /\ v IN s /\ u <= v ==> f u <= f v) \/
      (!u v. u IN s /\ v IN s /\ u <= v ==> f v <= f u))
     ==> &0 <= f x * (x - y) pow k * (x - z) pow k +
               f y * (y - z) pow k * (y - x) pow k +
               f z * (z - x) pow k * (z - y) pow k`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u v w. u IN s /\ v IN s /\ w IN s /\ w <= v /\ v <= u
            ==> (f:real->real) v <= f u \/ f v <= f w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
                  check (is_disj o concl)) THENL
     [MP_TAC(ISPECL [`f:real->real`; `s:real->bool`; `u:real`; `w:real`;
                     `v:real`] REAL_CONVEX_LOWER_REAL_SEGMENT) THEN
      ASM_REWRITE_TAC[IN_REAL_SEGMENT] THEN
      TRY(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN REAL_ARITH_TAC;
      DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  let try_order (a,b,c) =
    MP_TAC(SPECL [`f:real->real`; a; b; c; `k:num`]
                 SCHUR_VORNICU_INEQUALITY_GEN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC] in
  MAP_EVERY (fun (a,b) -> DISJ_CASES_TAC(SPECL [a;b] REAL_LE_TOTAL))
   [`x:real`,`y:real`; `y:real`,`z:real`; `x:real`,`z:real`] THEN
  FIRST (map try_order
   [`x:real`,`y:real`,`z:real`; `x:real`,`z:real`,`y:real`;
    `y:real`,`x:real`,`z:real`; `y:real`,`z:real`,`x:real`;
    `z:real`,`x:real`,`y:real`; `z:real`,`y:real`,`x:real`]));;

(* ------------------------------------------------------------------------- *)
(* Sums and integrals of an increasing f: int_a^(a+n) f <= sum_(k=1..n)      *)
(* f(a+k) <= int_(a+1)^(a+n+1) f.                                            *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_LE_SUM_INCREASING = prove
 (`!f a n.
     (!x y. a <= x /\ x <= y /\ y <= a + &n ==> f x <= f y)
     ==> real_integral (real_interval[a,a + &n]) f <=
         sum(1..n) (\k. f(a + &k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real) real_integrable_on real_interval[a,a + &n]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INCREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --((f:real->real) x)`; `a:real`; `n:num`]
                SUM_LE_REAL_INTEGRAL_DECREASING) THEN
  ASM_SIMP_TAC[REAL_LE_NEG2; SUM_NEG; REAL_INTEGRAL_NEG]);;

let SUM_LE_REAL_INTEGRAL_INCREASING = prove
 (`!f a n.
     (!x y. a + &1 <= x /\ x <= y /\ y <= a + &n + &1 ==> f x <= f y)
     ==> sum(1..n) (\k. f(a + &k)) <=
         real_integral (real_interval[a + &1,a + &n + &1]) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:real->real) real_integrable_on real_interval[a + &1,a + &n + &1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_INCREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. --((f:real->real) x)`; `a:real`; `n:num`]
                REAL_INTEGRAL_LE_SUM_DECREASING) THEN
  ASM_SIMP_TAC[REAL_LE_NEG2; SUM_NEG; REAL_INTEGRAL_NEG]);;

let SUM_INTEGRAL_INEQUALITY = prove
 (`!f a n.
     (!x y. a <= x /\ x <= y /\ y <= a + &n + &1 ==> f x <= f y)
     ==> real_integral (real_interval[a,a + &n]) f <=
         sum(1..n) (\k. f(a + &k)) /\
         sum(1..n) (\k. f(a + &k)) <=
         real_integral (real_interval[a + &1,a + &n + &1]) f`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE_SUM_INCREASING;
    MATCH_MP_TAC SUM_LE_REAL_INTEGRAL_INCREASING] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hermite-Hadamard: f((a+b)/2) <= (1/(b-a)) int_a^b f <= (f(a)+f(b))/2 for  *)
(* convex f.                                                                 *)
(* ------------------------------------------------------------------------- *)

let HERMITE_INEQUALITY_MUL = prove
 (`!f a b.
     a <= b /\ f real_convex_on real_interval[a,b]
     ==> (b - a) * f((a + b) / &2) <=
         real_integral (real_interval[a,b]) f /\
         real_integral (real_interval[a,b]) f <=
         (b - a) * (f a + f b) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_SUB_REFL; REAL_MUL_LZERO;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) < b` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval[a,b]`]
                REAL_INTEGRABLE_INTEGRAL) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONVEX] THEN
  ABBREV_TAC `i = real_integral (real_interval[a,b]) f` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `i:real`; `a:real`; `b:real`; `--(&1)`;
                   `a + b:real`] HAS_REAL_INTEGRAL_AFFINITY) THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_INV_NEG; REAL_INV_1;
                    REAL_MUL_LID] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN
     `IMAGE (\x. --(&1) * (x - (a + b))) (real_interval[a,b]) =
      real_interval[a,b]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        DISCH_TAC THEN EXISTS_TAC `a + b - y:real` THEN ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    SUBGOAL_THEN `(&2 * (f:real->real)((a + b) / &2)) * (b - a) <= i + i`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real. &2 * (f:real->real)((a + b) / &2)`;
      `\x. (f:real->real) x + f(--(&1) * x + a + b)`;
      `real_interval[a:real,b]`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:real`; `--(&1) * x + a + b`; `&1 / &2`;
                                `&1 / &2`] o
                GEN_REWRITE_RULE I [real_convex_on]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 * x + &1 / &2 * (--(&1) * x + a + b) = (a + b) / &2`
    SUBST1_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. ((f:real->real) a * (b * x - x pow 2 / &2) +
          f b * (x pow 2 / &2 - a * x)) / (b - a)`;
    `\x. (b - x) / (b - a) * (f:real->real) a + (x - a) / (b - a) * f b`;
    `a:real`; `b:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    UNDISCH_TAC `(a:real) < b` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `((f:real->real) a * (b * b - b pow 2 / &2) +
     f b * (b pow 2 / &2 - a * b)) / (b - a) -
    (f a * (b * a - a pow 2 / &2) +
     f b * (a pow 2 / &2 - a * a)) / (b - a)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `(a:real) < b` THEN
    CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`f:real->real`;
    `\x. (b - x) / (b - a) * (f:real->real) a + (x - a) / (b - a) * f b`;
    `real_interval[a:real,b]`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `((b:real) - x) / (b - a)`;
                              `((x:real) - a) / (b - a)`] o
              GEN_REWRITE_RULE I [real_convex_on]) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  SUBGOAL_THEN
   `((b:real) - x) / (b - a) + (x - a) / (b - a) = &1 /\
    ((b:real) - x) / (b - a) * a + (x - a) / (b - a) * b = x`
  (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `(a:real) < b` THEN CONV_TAC REAL_FIELD);;

let HERMITE_INEQUALITY = prove
 (`!f a b.
     a < b /\ f real_convex_on real_interval[a,b]
     ==> f((a + b) / &2) <= real_integral (real_interval[a,b]) f / (b - a) /\
         real_integral (real_interval[a,b]) f / (b - a) <= (f a + f b) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`]
                HERMITE_INEQUALITY_MUL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ;
               REAL_SUB_LT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Young's inequality for a continuous strictly increasing f with f(0) = 0   *)
(* and inverse g: ab <= int_0^a f + int_0^b g.                               *)
(* ------------------------------------------------------------------------- *)

let YOUNG_INTEGRAL_INEQUALITY = prove
 (`!f g c a b.
     f real_continuous_on real_interval[&0,c] /\
     (!x y. x IN real_interval[&0,c] /\ y IN real_interval[&0,c] /\ x < y
            ==> f x < f y) /\
     f(&0) = &0 /\ (!x. x IN real_interval[&0,c] ==> g(f x) = x) /\
     &0 <= a /\ a <= c /\ &0 <= b /\ b <= f c
     ==> a * b <= real_integral (real_interval[&0,a]) f +
                  real_integral (real_interval[&0,b]) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cont") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "strict" o REWRITE_RULE[IN_REAL_INTERVAL]) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "inv" o REWRITE_RULE[IN_REAL_INTERVAL]) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x y. &0 <= x /\ x <= c /\ &0 <= y /\ y <= c /\ x <= y
          ==> (f:real->real) x <= f y`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = y` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "strict" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= (f:real->real) c
        ==> &0 <= (g:real->real) s /\ g s <= c /\ f(g s) = s`
  (LABEL_TAC "ginv") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `&0`; `c:real`; `s:real`]
                  REAL_IVT_INCREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y s. &0 <= x /\ y <= c /\ x <= y /\ (f:real->real) x <= s /\ s <= f y
            ==> x <= (g:real->real) s /\ g s <= y`
  (LABEL_TAC "rng") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real->real)(&0) <= f x /\ f y <= f c`
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
   `!u v. &0 <= u /\ v <= c
          ==> (f:real->real) real_integrable_on real_interval[u,v]`
  (LABEL_TAC "intf") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,c]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. &0 <= u /\ v <= (f:real->real) c
          ==> (g:real->real) real_integrable_on real_interval[u,v]`
  (LABEL_TAC "intg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_INCREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "ginv" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "rng"
     (MP_TAC o SPECL [`(g:real->real) s`; `c:real`; `t:real`]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 <= x /\ x <= c
        ==> real_integral (real_interval[&0,x]) f +
            real_integral (real_interval[&0,(f:real->real) x]) g -
            x * f x = &0`
  (LABEL_TAC "id") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `g:real->real`; `&0`; `x:real`]
                  REAL_INTEGRAL_ADD_INVERSE_FUNCTION) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `real_interval[&0,c]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "strict" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "inv" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (f:real->real) a` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real->real)(&0) <= f a` MP_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `b <= (f:real->real) a \/ f a <= b`) THENL
   [MP_TAC(ISPECL [`f:real->real`; `&0`; `a:real`; `b:real`]
                  REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[&0,c]` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)] THEN
    USE_THEN "id" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `&0`; `a:real`; `t:real`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "intf" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(INST [`b:real`,`B:real`]
           (ISPECL [`f:real->real`; `t:real`; `a:real`]
                   REAL_INTEGRAL_LBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o
          check (fun th -> concl th = `(f:real->real) t = b`)) THEN
        USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    USE_THEN "id" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`g:real->real`; `&0`; `b:real`; `(f:real->real) a`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "intg" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(INST [`a:real`,`B:real`]
           (ISPECL [`g:real->real`; `(f:real->real) a`; `b:real`]
                   REAL_INTEGRAL_LBOUND)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "intg" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        USE_THEN "rng" (MP_TAC o SPECL [`a:real`; `c:real`; `s:real`]) THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

let YOUNG_INTEGRAL_INEQUALITY_ALT = prove
 (`!f g a b.
     f real_continuous_on {x | &0 <= x} /\
     (!x y. &0 <= x /\ x < y ==> f x < f y) /\
     f(&0) = &0 /\ (!x. &0 <= x ==> g(f x) = x) /\
     &0 <= a /\ (?c. &0 <= c /\ f c = b)
     ==> a * b <= real_integral (real_interval[&0,a]) f +
                  real_integral (real_interval[&0,b]) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "strict") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f:real->real)(&0) <= f c /\ f c <= f(max a c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `c:real = &0` THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "strict" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `c = max a c` THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "strict" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC YOUNG_INTEGRAL_INEQUALITY THEN
  EXISTS_TAC `max a c` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real | &0 <= x}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "strict" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Pinsker's inequality: (sum |a_i - b_i|)^2 / 2 <= the relative entropy of  *)
(* a with respect to b, in nats and in bits.                                 *)
(* ------------------------------------------------------------------------- *)

let TWO_POINT_LOG_RATIO_GE_SQUARE = prove
 (`!p q. &0 <= q /\ q <= p /\ p <= &1 /\ (q = &0 ==> p = &0)
         ==> &2 * (p - q) pow 2 <=
             p * log(p / q) + (&1 - p) * log((&1 - p) / (&1 - q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q:real = &0` THENL
   [FIRST_X_ASSUM(fun th ->
      ASSUME_TAC(MATCH_MP th (ASSUME `q:real = &0`))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `q:real = &1` THENL
   [SUBGOAL_THEN `p:real = &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q /\ q < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p:real = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_LT_01; LOG_1] THEN
    MP_TAC(ISPECL [`\t. log t + &2 * (&1 - t) pow 2`;
                   `\t. inv t - &4 * (&1 - t)`; `real_interval[q,&1]`;
                   `q:real`; `&1`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; LOG_1] THEN
    ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `inv x - &4 * (&1 - x) = (&1 - &2 * x) pow 2 / x`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(q:real) <= x` THEN UNDISCH_TAC `&0 < q` THEN
        CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p /\ &0 < &1 - p /\ &0 < &1 - q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN
  MP_TAC(ISPECL
   [`\t. p * log t + (&1 - p) * log(&1 - t) + &2 * (p - t) pow 2`;
    `\t. p / t - (&1 - p) / (&1 - t) - &4 * (p - t)`;
    `real_interval[q,p]`; `q:real`; `p:real`]
   HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      UNDISCH_TAC `(q:real) <= x` THEN UNDISCH_TAC `(x:real) <= p` THEN
      UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < &1 - p` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `p / x - (&1 - p) / (&1 - x) - &4 * (p - x) =
      (p - x) * (&1 - &2 * x) pow 2 / (x * (&1 - x))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(q:real) <= x` THEN UNDISCH_TAC `(x:real) <= p` THEN
      UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < &1 - p` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_LE_POW_2];
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]];
    ASM_REAL_ARITH_TAC]);;

let PINSKER_INEQUALITY_LOG = prove
 (`!(k:A->bool) a b.
     FINITE k /\
     (!i. i IN k ==> &0 <= a i /\ &0 <= b i /\ (b i = &0 ==> a i = &0)) /\
     sum k a = &1 /\ sum k b = &1
     ==> sum k (\i. abs(a i - b i)) pow 2 / &2 <=
         sum k (\i. a i * log(a i / b i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = {i | i IN k /\ (b:A->real) i <= a i}` THEN
  ABBREV_TAC `v = {i | i IN k /\ ~((b:A->real) i <= a i)}` THEN
  SUBGOAL_THEN `!h:A->real. sum k h = sum u h + sum v h`
  (LABEL_TAC "split") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`k:A->bool`; `\i. (b:A->real) i <= a i`; `h:A->real`;
                   `h:A->real`] SUM_CASES) THEN
    ASM_REWRITE_TAC[COND_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (u:A->bool) /\ FINITE (v:A->bool) /\ u SUBSET k /\ v SUBSET k /\
    (!i. i IN u ==> (b:A->real) i <= a i) /\ (!i. i IN v ==> a i < b i)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; SUBSET; IN_ELIM_THM; REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum v (a:A->real) = &1 - sum u a /\ sum v (b:A->real) = &1 - sum u b`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "split" (MP_TAC o SPEC `a:A->real`) THEN
    USE_THEN "split" (MP_TAC o SPEC `b:A->real`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum k (\i. abs((a:A->real) i - b i)) = &2 * (sum u a - sum u b)`
  SUBST1_TAC THENL
   [USE_THEN "split" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `sum u (\i. abs((a:A->real) i - b i)) = sum u a - sum u b /\
      sum v (\i. abs((a:A->real) i - b i)) = sum v b - sum v a`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC[GSYM SUM_SUB] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `j:A` THEN DISCH_TAC THEN REWRITE_TAC[] THENL
       [UNDISCH_TAC `!i. i IN u ==> (b:A->real) i <= a i`;
        UNDISCH_TAC `!i. i IN v ==> (a:A->real) i < b i`] THEN
      DISCH_THEN(MP_TAC o SPEC `j:A`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i IN u
         ==> &0 <= (a:A->real) i /\ &0 <= b i /\ (b i = &0 ==> a i = &0)) /\
    (!i. i IN v
         ==> &0 <= (a:A->real) i /\ &0 <= b i /\ (b i = &0 ==> a i = &0))`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum u (b:A->real) /\ sum u b <= sum u a /\ &0 <= sum v (a:A->real)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUM_POS_LE THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sum u (b:A->real) = &0 ==> sum u (a:A->real) = &0) /\
    (sum u b = &1 ==> sum u a = &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `!i. i IN u ==> (b:A->real) i = &0` ASSUME_TAC THENL
       [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `!i. i IN v ==> (b:A->real) i = &0` ASSUME_TAC THENL
       [MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sum v (a:A->real) = &0` MP_TAC THENL
       [MATCH_MP_TAC SUM_EQ_0 THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sum u (a:A->real)`; `sum u (b:A->real)`]
                TWO_POINT_LOG_RATIO_GE_SQUARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `a:A->real`; `b:A->real`] GIBBS_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:A->bool`; `a:A->real`; `b:A->real`] GIBBS_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "split" (fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC);;

let PINSKER_INEQUALITY = prove
 (`!(k:A->bool) a b.
     FINITE k /\
     (!i. i IN k ==> &0 <= a i /\ &0 <= b i /\ (b i = &0 ==> a i = &0)) /\
     sum k a = &1 /\ sum k b = &1
     ==> sum k (\i. abs(a i - b i)) pow 2 / &2 <=
         sum k (\i. a i * log(a i / b i) / log(&2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PINSKER_INEQUALITY_LOG) THEN
  SUBGOAL_THEN `&0 < log(&2) /\ log(&2) <= &1` STRIP_ASSUME_TAC THENL
   [MP_TAC LOG_2_POS THEN MP_TAC LOG_2_RATIONAL_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; SUM_RMUL] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `sum k (\i. abs((a:A->real) i - b i))` REAL_LE_POW_2) THEN
  ABBREV_TAC `s = sum k (\i. (a:A->real) i * log(a i / b i))` THEN
  ABBREV_TAC `d = sum k (\i. abs((a:A->real) i - b i)) pow 2` THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`d / &2`; `log(&2)`; `&1`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Majorization. If b is nonincreasing and a majorizes b, then a is reached  *)
(* from b by transfers between two coordinates; hence Karamata's inequality  *)
(* and Muirhead's inequality.                                                *)
(* ------------------------------------------------------------------------- *)

let NONINCREASING_NUMSEG = prove
 (`!(b:num->real) n.
     (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i)
     ==> !i j. 1 <= i /\ i <= j /\ j <= n ==> b j <= b i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `i = SUC j` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(b:num->real) j` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let MAJORIZATION_INDUCT = prove
 (`!P n (b:num->real).
     (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\
     (!a. (!i. 1 <= i /\ i <= n ==> a i = b i) ==> P a) /\
     (!a j k t.
        1 <= j /\ j < k /\ k <= n /\ &0 < t /\ a k + t <= a j - t /\
        P (\i. if i = j then a j - t else if i = k then a k + t else a i)
        ==> P a)
     ==> !a. (!s. s <= n ==> sum(1..s) b <= sum(1..s) a) /\
             sum(1..n) a = sum(1..n) b
             ==> P a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bdec")
   (CONJUNCTS_THEN2 (LABEL_TAC "base") (LABEL_TAC "step"))) THEN
  SUBGOAL_THEN
   `!m a. CARD {i | i IN 1..n /\ ~((a:num->real) i = b i)} = m /\
          (!s. s <= n ==> sum(1..s) b <= sum(1..s) a) /\
          sum(1..n) a = sum(1..n) b
          ==> P a`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN X_GEN_TAC `a:num->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
   (CONJUNCTS_THEN2 (LABEL_TAC "maj") (LABEL_TAC "tot"))) THEN
  ASM_CASES_TAC `!i. 1 <= i /\ i <= n ==> (a:num->real) i = b i` THENL
   [USE_THEN "base" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= n /\ (a:num->real) k < b k` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT;
                TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `sum(1..n) (b:num->real) < sum(1..n) a` MP_TAC THENL
     [MATCH_MP_TAC SUM_LT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[]; EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "kmin"))) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i < k ==> (b:num->real) i <= a i`
  (LABEL_TAC "below") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    SUBGOAL_THEN `(i:num) <= n` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j < k /\ (b:num->real) j < a j` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `sum(1..k-1) (a:num->real) = sum(1..k-1) b` ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `1 <= i /\ i < k` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_MESON_TAC[];
        USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "maj" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 <= k`;
             ARITH_RULE `1 <= k ==> 0 < k`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?j. (1 <= j /\ j < k /\ (b:num->real) j < a j) /\
        (!x. 1 <= x /\ x < k /\ b x < a x ==> x <= j)`
  (X_CHOOSE_THEN `j:num`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "jmax"))) THENL
   [MP_TAC(ISPEC `\j. 1 <= j /\ j < k /\ (b:num->real) j < a j` num_MAX) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN MESON_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. j < i /\ i < k ==> (a:num->real) i = b i`
  (LABEL_TAC "mid") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "jmax" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      USE_THEN "below" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:num->real) k <= b j` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:num->real`; `n:num`] NONINCREASING_NUMSEG) THEN
    ANTS_TAC THENL
     [USE_THEN "bdec" ACCEPT_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t = min ((a:num->real) j - b j) (b k - a k)` THEN
  SUBGOAL_THEN
   `&0 < t /\ t <= (a:num->real) j - b j /\ t <= b k - a k /\
    (t = a j - b j \/ t = b k - a k)`
  (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "step" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `k:num`; `t:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `c = \i. if i = j then (a:num->real) j - t
            else if i = k then a k + t else a i` THEN
  SUBGOAL_THEN
   `!s. sum(1..s) (c:num->real) =
        sum(1..s) a + (if k IN 1..s then t else &0) -
        (if j IN 1..s then t else &0)`
  (LABEL_TAC "csum") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `c = \i. (a:num->real) i + (if i = k then t else &0) -
              (if i = j then t else &0)`
    SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY REAL_ARITH_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_DELTA]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (c:num->real) i =
        if i = j then a j - t else if i = k then a k + t else a i`
  (LABEL_TAC "cval") THENL [EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ih"
   (MP_TAC o SPEC `CARD {i | i IN 1..n /\ ~((c:num->real) i = b i)}`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[PSUBSET_ALT; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [EXISTS_TAC `j:num`; EXISTS_TAC `k:num`] THEN
      ASM_SIMP_TAC[ARITH_RULE `j < k ==> ~(k = j)`] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT CONJ_TAC THEN
      TRY(ASM_ARITH_TAC THEN NO_TAC) THEN TRY(DISJ2_TAC) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:num->real`) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `(k:num) IN 1..n /\ (j:num) IN 1..n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "csum" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN
  USE_THEN "csum" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "maj" (MP_TAC o SPEC `s:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `k <= s:num` THENL
   [ASM_SIMP_TAC[ARITH_RULE `j < k /\ k <= s ==> j <= s:num`] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `j <= s:num` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `sum(j+1..s) (a:num->real) = sum(j+1..s) b` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    USE_THEN "mid" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num->real`; `1`; `j:num`; `s:num`] SUM_COMBINE_R) THEN
  MP_TAC(ISPECL [`b:num->real`; `1`; `j:num`; `s:num`] SUM_COMBINE_R) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= j + 1`] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  USE_THEN "maj" (MP_TAC o SPEC `j - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 <= j`;
           ARITH_RULE `1 <= j ==> 0 < j`] THEN
  ASM_REAL_ARITH_TAC);;

let KARAMATA_INEQUALITY = prove
 (`!f s n a b.
     is_realinterval s /\ f real_convex_on s /\
     (!i. 1 <= i /\ i <= n ==> a i IN s /\ b i IN s) /\
     (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\
     (!t. t <= n ==> sum(1..t) b <= sum(1..t) a) /\
     sum(1..n) a = sum(1..n) b
     ==> sum(1..n) (\i. f(b i)) <= sum(1..n) (\i. f(a i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\a:num->real. (!i. 1 <= i /\ i <= n ==> a i IN s)
                   ==> sum(1..n) (\i. (f:real->real)(b i)) <=
                       sum(1..n) (\i. f(a i))`;
    `n:num`; `b:num->real`] MAJORIZATION_INDUCT) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN ASM_SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `j:num`; `k:num`; `t:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:num->real) j IN s /\ c k IN s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. (c:num->real) k <= x /\ x <= c j ==> x IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[is_realinterval] o
      check (fun th -> concl th = `is_realinterval s`)) THEN
    MAP_EVERY EXISTS_TAC [`(c:num->real) k`; `(c:num->real) j`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_forall(fst(dest_imp(concl th))))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REPEAT COND_CASES_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `!i. 1 <= i /\ i <= n ==> (c:num->real) i IN s` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. (f:real->real)
                   (if i = j then c j - t else if i = k then c k + t
                    else c i)) =
    sum(1..n) (\i. f(c i) + (if i = j then f(c j - t) - f(c j) else &0) +
                   (if i = k then f(c k + t) - f(c k) else &0))`
  SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `~(j:num = k) /\ ~(k = j)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `i:num = j` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= j /\ j <= n /\ 1 <= k /\ k <= n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `f:real->real`)) (concl th) &&
    is_binary "real_le" (concl th))) THEN
  ASM_REWRITE_TAC[SUM_ADD_NUMSEG; SUM_DELTA; IN_NUMSEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(f:real->real)((c:num->real) j - t) + f(c k + t) <= f(c j) + f(c k)`
  MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 < (c:num->real) j - c k` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = ((c:num->real) j - c k - t) / (c j - c k)` THEN
  SUBGOAL_THEN
   `&0 <= u /\ &0 <= &1 - u /\
    u * (c:num->real) k + (&1 - u) * c j = c k + t /\
    (&1 - u) * c k + u * c j = c j - t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < (c:num->real) j - c k` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < (c:num->real) j - c k` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(c:num->real) k`; `(c:num->real) j`;
                              `u:real`; `&1 - u`] o
              GEN_REWRITE_RULE I [real_convex_on]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `u + &1 - u = &1`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(c:num->real) k`; `(c:num->real) j`;
                              `&1 - u`; `u:real`] o
              GEN_REWRITE_RULE I [real_convex_on]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 - u + u = &1`] THEN DISCH_TAC THEN
  ASM_REAL_ARITH_TAC);;

let KARAMATA_INEQUALITY_CONCAVE = prove
 (`!f s n a b.
     is_realinterval s /\ (\t. --f t) real_convex_on s /\
     (!i. 1 <= i /\ i <= n ==> a i IN s /\ b i IN s) /\
     (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\
     (!t. t <= n ==> sum(1..t) b <= sum(1..t) a) /\
     sum(1..n) a = sum(1..n) b
     ==> sum(1..n) (\i. f(a i)) <= sum(1..n) (\i. f(b i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real. --(f:real->real) t`; `s:real->bool`; `n:num`;
                 `a:num->real`; `b:num->real`] KARAMATA_INEQUALITY) THEN
  ASM_REWRITE_TAC[SUM_NEG; REAL_LE_NEG2]);;

let MUIRHEAD_INEQUALITY = prove
 (`!n x a b.
     (!i. 1 <= i /\ i <= n ==> &0 <= x i) /\
     ((!i. 1 <= i /\ i <= n ==> &0 < x i) \/
      (!i. 1 <= i /\ i <= n ==> &0 <= a i)) /\
     (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\
     (!t. t <= n ==> sum(1..t) b <= sum(1..t) a) /\
     sum(1..n) a = sum(1..n) b
     ==> sum {p | p permutes 1..n}
             (\p. product(1..n) (\i. x(p i) rpow b i)) <=
         sum {p | p permutes 1..n}
             (\p. product(1..n) (\i. x(p i) rpow a i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "xpos")
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`\a:num->real.
       ((!i. 1 <= i /\ i <= n ==> &0 < x i) \/
        (!i. 1 <= i /\ i <= n ==> &0 <= a i))
       ==> sum {p | p permutes 1..n}
               (\p. product(1..n) (\i. (x:num->real)(p i) rpow b i)) <=
           sum {p | p permutes 1..n}
               (\p. product(1..n) (\i. x(p i) rpow a i))`;
    `n:num`; `b:num->real`] MAJORIZATION_INDUCT) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `j:num`; `k:num`; `t:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "posc") THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && is_disj(fst(dest_imp(concl th))))) THEN
  ANTS_TAC THENL
   [USE_THEN "posc" (DISJ_CASES_THEN ASSUME_TAC) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= (c:num->real) k /\ &0 <= c i` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    MATCH_MP (REAL_ARITH `(x:real) <= y ==> y <= z ==> x <= z`)) THEN
  SUBGOAL_THEN `&0 < (c:num->real) j - c k` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `mu = t / ((c:num->real) j - c k)` THEN
  SUBGOAL_THEN `&0 < mu /\ mu < &1 /\ mu * ((c:num->real) j - c k) = t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (if i = j then (c:num->real) j - t else if i = k then c k + t
         else c i) =
        (&1 - mu) * c i + mu * c(swap(j,k) i)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[swap] THEN
    SUBGOAL_THEN `~(j:num = k)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `swap(j,k) permutes 1..n` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. swap(j,k) (swap(j,k) i) = i` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`j:num`; `k:num`] SWAP_IDEMPOTENT) THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {p | p permutes 1..n}
        (\p. product(1..n) (\i. (x:num->real)(p i) rpow c(swap(j,k) i))) =
    sum {p | p permutes 1..n} (\p. product(1..n) (\i. x(p i) rpow c i))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\p:num->num. product(1..n) (\i. (x:num->real)(p i) rpow c i)`;
      `1`; `n:num`; `swap(j:num,k)`]
     SUM_PERMUTATIONS_COMPOSE_R) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\i. (x:num->real)(p i) rpow c(swap(j:num,k) i)`;
                   `swap(j:num,k)`; `1..n`] PRODUCT_PERMUTE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {p | p permutes 1..n}
        (\p. (&1 - mu) * product(1..n) (\i. (x:num->real)(p i) rpow c i) +
             mu * product(1..n) (\i. x(p i) rpow c(swap(j,k) i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; FINITE_PERMUTATIONS; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_SUB_ADD; REAL_MUL_LID;
                REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; IN_ELIM_THM] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `product(1..n)
      (\i. (x:num->real)(p i) rpow ((&1 - mu) * c i + mu * c(swap(j,k) i))) =
    product(1..n)
      (\i. (x(p i) rpow c i) rpow (&1 - mu) *
           (x(p i) rpow c(swap(j,k) i)) rpow mu)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:num->num) i IN 1..n /\ swap(j,k) i IN 1..n` MP_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= (x:num->real)(p(i:num))` ASSUME_TAC THENL
     [USE_THEN "xpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_RPOW] THEN
    SUBGOAL_THEN
     `(&1 - mu) * (c:num->real) i + mu * c(swap(j,k) i) =
      c i * (&1 - mu) + c(swap(j,k) i) * mu`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RPOW_ADD_ALT THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "posc" (DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(MP_TAC o SPEC `(p:num->num) i`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> MP_TAC(SPEC `i:num` th) THEN
                           MP_TAC(SPEC `swap(j,k) (i:num)` th)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`(c:num->real) i`; `&1 - mu`] REAL_LE_MUL) THEN
      MP_TAC(ISPECL [`(c:num->real)(swap(j,k) i)`; `mu:real`] REAL_LE_MUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG] THEN
  SIMP_TAC[GSYM RPOW_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC RPOW_MUL_RPOW_LE_WEIGHTED_SUM THEN REPEAT CONJ_TAC THEN
  TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN
  USE_THEN "xpos" MATCH_MP_TAC THEN
  ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]);;
