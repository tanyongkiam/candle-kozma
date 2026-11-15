(* ========================================================================= *)
(* Inequalities about finite sums and products of real numbers, from         *)
(* L. Kozma, "Useful Inequalities" (v0.44).                                  *)
(* ========================================================================= *)

needs "Library/permutations.ml";;
needs "Library/products.ml";;

(* ------------------------------------------------------------------------- *)
(* Cauchy-Schwarz inequality: (sum x_i y_i)^2 <= (sum x_i^2) (sum y_i^2),    *)
(* over any finite index set.                                                *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_SCHWARZ_INEQUALITY = prove
 (`!s (x:A->real) y.
        FINITE s
        ==> sum s (\i. x i * y i) pow 2
            <= sum s (\i. x i pow 2) * sum s (\i. y i pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum s (\i:A. sum s (\j. (x i * y j - x j * y i) pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a * b - c * d) pow 2 =
    a pow 2 * b pow 2 + c pow 2 * d pow 2 - (&2 * a * d) * (c * b)`] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_ADD; SUM_LMUL; SUM_RMUL] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `&0 <= a * b + a * b - (&2 * c) * c ==> c pow 2 <= a * b`));;

(* ------------------------------------------------------------------------- *)
(* Cauchy-Schwarz in Engel form, (sum d_i)^2 <= (sum w_i)(sum d_i^2 / w_i)   *)
(* for w_i >= 0 with d_i = 0 wherever w_i = 0, and its special case the      *)
(* harmonic-mean bound n^2 <= (sum c_i)(sum 1 / c_i) for c_i > 0.            *)
(* ------------------------------------------------------------------------- *)

let SUM_SQUARE_LE_SUM_DIV = prove
 (`!s (w:A->real) d.
        FINITE s /\ (!i. i IN s ==> &0 <= w i /\ (w i = &0 ==> d i = &0))
        ==> sum s d pow 2 <= sum s w * sum s (\i. d i pow 2 / w i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i:A. sqrt(w i)`; `\i:A. d i / sqrt(w i)`]
    CAUCHY_SCHWARZ_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum s (\i:A. sqrt(w i) * d i / sqrt(w i)) = sum s d /\
    sum s (\i:A. sqrt(w i) pow 2) = sum s w /\
    sum s (\i:A. (d i / sqrt(w i)) pow 2) = sum s (\i. d i pow 2 / w i)`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_DIV] THEN
  ASM_CASES_TAC `(w:A->real) i = &0` THEN
  ASM_SIMP_TAC[SQRT_0; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_SIMP_TAC[SQRT_EQ_0]);;

let SUM_INV_CARD_LE = prove
 (`!s (c:A->real).
        FINITE s /\ (!i. i IN s ==> &0 < c i)
        ==> &(CARD s) pow 2 <= sum s c * sum s (\i. inv(c i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `c:A->real`; `\i:A. &1`]
    SUM_SQUARE_LE_SUM_DIV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ; SUM_CONST; REAL_MUL_RID;
               REAL_POW_ONE; real_div; REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Samuelson's inequality: every point lies within sigma * sqrt(n - 1) of    *)
(* the mean, where sigma is the (population) standard deviation. The two     *)
(* one-sided bounds of the sheet are stated together as one bound on         *)
(* abs(x i - mu).                                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_ZERO_SQUARE_LE = prove
 (`!s (d:A->real) i.
        FINITE s /\ i IN s /\ sum s d = &0
        ==> &(CARD s) * d i pow 2 <= (&(CARD s) - &1) * sum s (\j. d j pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s DELETE (i:A)`; `d:A->real`; `(\j:A. &1)`]
    CAUCHY_SCHWARZ_INEQUALITY) THEN
  ASM_SIMP_TAC[FINITE_DELETE; SUM_DELETE; SUM_CONST; CARD_DELETE;
               REAL_MUL_RID; REAL_POW_ONE; ETA_AX] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `(&0 - d) pow 2 <= (t - d pow 2) * (c - &1)
    ==> c * d pow 2 <= (c - &1) * t`));;

let SAMUELSON_INEQUALITY = prove
 (`!n (x:num->real) i.
        1 <= i /\ i <= n
        ==> abs(x i - sum(1..n) x / &n)
            <= sqrt(sum(1..n) (\j. (x j - sum(1..n) x / &n) pow 2) / &n) *
               sqrt(&n - &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `mu = sum(1..n) (x:num->real) / &n` THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..n) (\j. x j - mu) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB] THEN
    EXPAND_TAC "mu" THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..n`; `\j. (x:num->real) j - mu`; `i:num`]
    SUM_ZERO_SQUARE_LE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum(1..n) (\j. ((x:num->real) j - mu) pow 2) /\ &0 <= &n - &1`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2; REAL_SUB_LE;
             REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> s / n * m = (m * s) / n`;
               REAL_LE_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nesbitt's inequality, with S = sum a: sum a_i / (S - a_i) >= n / (n - 1), *)
(* and the equivalent form sum S / (S - a_i) >= n^2 / (n - 1). The sheet     *)
(* assumes a_i >= 0; only S - a_i > 0 is needed (the terms are undefined     *)
(* when S = a_i). For n = 1 that cannot hold; for n = 0 both sides are 0.    *)
(* ------------------------------------------------------------------------- *)

let NESBITT_INEQUALITY_ALT = prove
 (`!n (a:num->real).
        (!i. 1 <= i /\ i <= n ==> a i < sum(1..n) a)
        ==> &n pow 2 / (&n - &1)
            <= sum(1..n) (\i. sum(1..n) a / (sum(1..n) a - a i))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `2 <= n` THENL
   [STRIP_TAC THEN ABBREV_TAC `S = sum(1..n) (a:num->real)` THEN
    MP_TAC(ISPECL [`1..n`; `\i. S - (a:num->real) i`] SUM_INV_CARD_LE) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1; REAL_SUB_LT;
                 SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB; real_div;
                 SUM_LMUL] THEN
    SUBGOAL_THEN `&1 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
      (ARITH_RULE `~(2 <= n) ==> n = 0 \/ n = 1`)) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[SUM_SING_NUMSEG; LE_REFL] THEN REAL_ARITH_TAC]]);;

let NESBITT_INEQUALITY = prove
 (`!n (a:num->real).
        (!i. 1 <= i /\ i <= n ==> a i < sum(1..n) a)
        ==> &n / (&n - &1) <= sum(1..n) (\i. a i / (sum(1..n) a - a i))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `2 <= n` THENL
   [ALL_TAC;
    FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP
      (ARITH_RULE `~(2 <= n) ==> n = 0 \/ n = 1`)) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[SUM_SING_NUMSEG; LE_REFL] THEN REAL_ARITH_TAC]] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NESBITT_INEQUALITY_ALT) THEN
  ABBREV_TAC `S = sum(1..n) (a:num->real)` THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. S / (S - (a:num->real) i)) -
    sum(1..n) (\i. a i / (S - a i)) = &n`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    TRANS_TAC EQ_TRANS `sum(1..n) (\i. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_FIELD `a < s ==> s / (s - a) - a / (s - a) = &1`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD
    `&1 < n ==> n pow 2 / (n - &1) = n / (n - &1) + n`] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Kantorovich's inequality: if 0 < m <= x_i / y_i <= M, then                *)
(* (sum x_i^2)(sum y_i^2) <= (A/G)^2 (sum x_i y_i)^2 with A = (m + M) / 2    *)
(* and G = sqrt(m M), i.e. (A/G)^2 = (m + M)^2 / (4 m M).                    *)
(* ------------------------------------------------------------------------- *)

let KANTOROVICH_INEQUALITY = prove
 (`!s (x:A->real) y m M.
        FINITE s /\ &0 < m /\
        (!i. i IN s ==> m <= x i / y i /\ x i / y i <= M)
        ==> sum s (\i. x i pow 2) * sum s (\i. y i pow 2)
            <= (m + M) pow 2 / (&4 * m * M) * sum s (\i. x i * y i) pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real) <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum s (\i:A. (x i - m * y i) * (M * y i - x i))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((y:A->real) i = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `m <= (x:A->real) i / y i` THEN
      ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `r = (x:A->real) i / y i` THEN
    SUBGOAL_THEN `(x:A->real) i = r * y i` SUBST1_TAC THENL
     [EXPAND_TAC "r" THEN UNDISCH_TAC `~((y:A->real) i = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `((r:real) * y - m * y) * (M * y - r * y) =
      y pow 2 * ((r - m) * (M - r))`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `((x:real) - m * y) * (M * y - x) =
    (m + M) * (x * y) - x pow 2 - (m * M) * y pow 2`] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_LMUL] THEN
  SUBGOAL_THEN
   `&0 <= sum s (\i:A. x i pow 2) /\ &0 <= sum s (\i:A. y i pow 2)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SPEC_TAC(`sum s (\i:A. x i * y i)`, `C:real`) THEN
  SPEC_TAC(`sum s (\i:A. y i pow 2)`, `Y:real`) THEN
  SPEC_TAC(`sum s (\i:A. x i pow 2)`, `X:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < m * M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) / b * c = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
               REAL_ARITH `&0 < m * M ==> &0 < &4 * m * M`] THEN
  TRANS_TAC REAL_LE_TRANS `((X:real) + (m * M) * Y) pow 2` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `(X:real) - (m * M) * Y` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Aczel's inequality: (a_1^2 - sum_{i>=2} a_i^2) (b_1^2 - sum_{i>=2} b_i^2) *)
(*   <= (a_1 b_1 - sum_{i>=2} a_i b_i)^2,                                    *)
(* given sum_{i>=2} a_i^2 <= a_1^2 (ACZEL_INEQUALITY) or                     *)
(* sum_{i>=2} b_i^2 <= b_1^2 (ACZEL_INEQUALITY_ALT). The sheet's hypotheses  *)
(* are strict; in the case of equality the left side is 0.                   *)
(* ------------------------------------------------------------------------- *)

let ACZEL_INEQUALITY = prove
 (`!n (a:num->real) b.
        sum(2..n) (\i. a i pow 2) <= a 1 pow 2
        ==> (a 1 pow 2 - sum(2..n) (\i. a i pow 2)) *
            (b 1 pow 2 - sum(2..n) (\i. b i pow 2))
            <= (a 1 * b 1 - sum(2..n) (\i. a i * b i)) pow 2`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `sum(2..n) (\i. (a:num->real) i pow 2) = a 1 pow 2` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_LE_POW_2];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(2..n) (\i. (a:num->real) i pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:num->real) 1 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(sum(2..n) (\i. (a:num->real) i pow 2) = a 1 pow 2)` THEN
    UNDISCH_TAC `sum(2..n) (\i. (a:num->real) i pow 2) <= a 1 pow 2` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = (b:num->real) 1 / a 1` THEN
  SUBGOAL_THEN `(a:num->real) 1 * t - b 1 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN UNDISCH_TAC `~((a:num->real) 1 = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(2..n) (\i. ((a:num->real) i * t - b i) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a * t - b) pow 2 = t pow 2 * a pow 2 - (&2 * t) * (a * b) + b pow 2`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC
   `(a 1 pow 2 - sum(2..n) (\i. (a:num->real) i pow 2)) * t -
    (a 1 * b 1 - sum(2..n) (\i. a i * b i))` REAL_LE_POW_2) THEN
  SUBGOAL_THEN
   `&0 <= (a 1 pow 2 - sum(2..n) (\i. (a:num->real) i pow 2)) *
          (t pow 2 * sum(2..n) (\i. a i pow 2) -
           (&2 * t) * sum(2..n) (\i. a i * b i) +
           sum(2..n) (\i. b i pow 2) - (a 1 * t - b 1) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let ACZEL_INEQUALITY_ALT = prove
 (`!n (a:num->real) b.
        sum(2..n) (\i. b i pow 2) <= b 1 pow 2
        ==> (a 1 pow 2 - sum(2..n) (\i. a i pow 2)) *
            (b 1 pow 2 - sum(2..n) (\i. b i pow 2))
            <= (a 1 * b 1 - sum(2..n) (\i. a i * b i)) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `b:num->real`; `a:num->real`] ACZEL_INEQUALITY) THEN
  REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Milne's inequality: for a_i, b_i >= 0,                                    *)
(* (sum (a_i + b_i)) (sum a_i b_i / (a_i + b_i)) <= (sum a_i) (sum b_i).     *)
(* A term with a_i + b_i = 0 is 0 / 0 = 0.                                   *)
(* ------------------------------------------------------------------------- *)

let MILNE_INEQUALITY = prove
 (`!s (a:A->real) b.
        FINITE s /\ (!i. i IN s ==> &0 <= a i /\ &0 <= b i)
        ==> sum s (\i. a i + b i) * sum s (\i. a i * b i / (a i + b i))
            <= sum s a * sum s b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\i. (a:A->real) i * b i / (a i + b i)) =
    sum s (\i. ((a i + b i) - (a i - b i) pow 2 / (a i + b i)) * inv(&4))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_CASES_TAC `(a:A->real) i + b i = &0` THENL
     [SUBGOAL_THEN `(a:A->real) i = &0 /\ b i = &0` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[real_div; REAL_ADD_LID; REAL_INV_0] THEN
        REAL_ARITH_TAC];
      UNDISCH_TAC `~((a:A->real) i + b i = &0)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i. (a:A->real) i + b i`;
                 `\i. (a:A->real) i - b i`] SUM_SQUARE_LE_SUM_DIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_RMUL; SUM_SUB; SUM_ADD] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `(p - q) pow 2 <= (p + q) * t
    ==> (p + q) * ((p + q) - t) * inv(&4) <= p * q`));;

(* ------------------------------------------------------------------------- *)
(* Abel's inequality: for b_1 >= ... >= b_n >= 0, sum a_i b_i lies between   *)
(* b_1 times the least and b_1 times the greatest partial sum of a. The      *)
(* bound form (any lower bound m and upper bound M of the partial sums) is   *)
(* proved first, by Abel summation.                                          *)
(* ------------------------------------------------------------------------- *)

let SUM_ABEL_PARTIAL = prove
 (`!(a:num->real) b n.
        sum(1..n+1) (\i. a i * b i) =
        sum(1..n+1) a * b(n+1) +
        sum(1..n) (\k. sum(1..k) a * (b k - b(k+1)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE
     [GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`]) THEN
    REAL_ARITH_TAC]);;

let SUM_MUL_DECREASING_BOUNDS = prove
 (`!n (a:num->real) b m M.
        1 <= n /\ (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\ &0 <= b n /\
        (!k. 1 <= k /\ k <= n ==> m <= sum(1..k) a /\ sum(1..k) a <= M)
        ==> b 1 * m <= sum(1..n) (\i. a i * b i) /\
            sum(1..n) (\i. a i * b i) <= b 1 * M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p. n = p + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_ABEL_PARTIAL] THEN
  SUBGOAL_THEN `(b:num->real) 1 = b(p + 1) + sum(1..p) (\k. b k - b(k + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_DIFFS] THEN COND_CASES_TAC THENL
     [REAL_ARITH_TAC;
      SUBGOAL_THEN `p = 0` SUBST1_TAC THENL
       [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  TRY(GEN_REWRITE_TAC LAND_CONV [GSYM SUM_RMUL] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[]) THEN
  TRY(GEN_REWRITE_TAC RAND_CONV [GSYM SUM_RMUL] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[]) THEN
  ((GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL) ORELSE
   (GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL)) THEN
  ASM_SIMP_TAC[REAL_SUB_LE; ARITH_RULE `i <= p ==> i < p + 1 /\ i <= p + 1`;
               LE_REFL; ARITH_RULE `1 <= p + 1`]);;

let ABEL_INEQUALITY = prove
 (`!n (a:num->real) b.
        1 <= n /\ (!i. 1 <= i /\ i < n ==> b(i + 1) <= b i) /\ &0 <= b n
        ==> b 1 * inf {sum(1..k) a | k IN 1..n} <= sum(1..n) (\i. a i * b i) /\
            sum(1..n) (\i. a i * b i) <= b 1 * sup {sum(1..k) a | k IN 1..n}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SUM_MUL_DECREASING_BOUNDS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN
  MP_TAC(ISPEC `IMAGE (\k. sum(1..k) (a:num->real)) (1..n)` INF_FINITE) THEN
  MP_TAC(ISPEC `IMAGE (\k. sum(1..k) (a:num->real)) (1..n)` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
               GSYM NOT_LE; FORALL_IN_IMAGE; IN_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev's sum inequality: for nondecreasing f, g and weights p_i >= 0   *)
(* summing to 1, E[f(X)] E[g(X)] <= E[f(X) g(X)]. The sheet also assumes     *)
(* x_1 <= ... <= x_n; that is not needed, so the index set is any finite     *)
(* set. The general form is for any similarly ordered x, y.                  *)
(* ------------------------------------------------------------------------- *)

let SUM_SIMILARLY_ORDERED_LE = prove
 (`!s (p:A->real) x y.
        FINITE s /\ (!i. i IN s ==> &0 <= p i) /\
        (!i j. i IN s /\ j IN s ==> &0 <= (x i - x j) * (y i - y j))
        ==> sum s (\i. p i * x i) * sum s (\i. p i * y i)
            <= sum s p * sum s (\i. p i * x i * y i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum s (\i:A. sum s (\j. p i * p j * (x i - x j) * (y i - y j)))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `j:A` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(p:real) * q * (f - f') * (g - g') =
    (p * f * g) * q - (p * f) * (q * g') - (p * g) * (q * f') +
    p * (q * f' * g')`] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; SUM_RMUL] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `&0 <= c * q - a * b - b * a + q * c ==> a * b <= q * c`));;

let CHEBYSHEV_SUM_INEQUALITY = prove
 (`!s (x:A->real) f g p.
        FINITE s /\ (!u v. u <= v ==> f u <= f v) /\
        (!u v. u <= v ==> g u <= g v) /\
        (!i. i IN s ==> &0 <= p i) /\ sum s p = &1
        ==> sum s (\i. f(x i) * p i) * sum s (\i. g(x i) * p i)
            <= sum s (\i. f(x i) * g(x i) * p i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `p:A->real`; `\i:A. (f:real->real)(x i)`;
                 `\i:A. (g:real->real)(x i)`] SUM_SIMILARLY_ORDERED_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN
    STRIP_TAC THEN
    DISJ_CASES_TAC
     (SPECL [`(x:A->real) i`; `(x:A->real) j`] REAL_LE_TOTAL) THENL
     [ONCE_REWRITE_TAC[REAL_ARITH
       `((a:real) - b) * (c - d) = (b - a) * (d - c)`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_SUB_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* The rearrangement inequality and its generalization. The general form: if *)
(* b is nondecreasing on 1..n and the family f satisfies the exchange        *)
(* condition f i y + f j x <= f i x + f j y for i <= j and x <= y, then over *)
(* all permutations p of 1..n, sum f i (b (p i)) is largest for p = I and    *)
(* smallest for the reversal i |-> (n + 1) - i. Proof by induction on n,     *)
(* moving the value b (n + 1) to position n + 1 by one exchange.             *)
(* ------------------------------------------------------------------------- *)

let SUM_LE_TWO_POINTS = prove
 (`!s (g:A->real) h k l.
        FINITE s /\ k IN s /\ l IN s /\
        (!i. i IN s /\ ~(i = k) /\ ~(i = l) ==> g i = h i) /\
        (k = l ==> g l = h l) /\ g k + g l <= h k + h l
        ==> sum s g <= sum s h`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:A = l` THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s DELETE (k:A)`; `l:A`] SUM_DELETE) THEN
  MP_TAC(ISPECL [`h:A->real`; `s DELETE (k:A)`; `l:A`] SUM_DELETE) THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `k:A`] SUM_DELETE) THEN
  MP_TAC(ISPECL [`h:A->real`; `s:A->bool`; `k:A`] SUM_DELETE) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  SUBGOAL_THEN
   `sum ((s DELETE k) DELETE l) (g:A->real) = sum ((s DELETE k) DELETE l) h`
  MP_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PERMUTES_NUMSEG_SWAP_TOP = prove
 (`!n p. p permutes 1..SUC n
         ==> ?k. k IN 1..SUC n /\ p k = SUC n /\
                 (swap(SUC n,p(SUC n)) o p) permutes 1..n /\
                 (swap(SUC n,p(SUC n)) o p) permutes 1..SUC n /\
                 (swap(SUC n,p(SUC n)) o p) (SUC n) = SUC n /\
                 (swap(SUC n,p(SUC n)) o p) k = p(SUC n) /\
                 p(SUC n) IN 1..SUC n /\
                 !i. i IN 1..SUC n /\ ~(i = k) /\ ~(i = SUC n)
                     ==> (swap(SUC n,p(SUC n)) o p) i = p i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. k IN 1..SUC n /\ p k = SUC n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_SURJECTIVE; PERMUTES_IN_IMAGE; IN_NUMSEG; LE_REFL;
                  ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->num) (SUC n) IN 1..SUC n` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_REFL;
                  ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PERMUTES_INSERT_LEMMA THEN
    ASM_SIMP_TAC[GSYM NUMSEG_REC; ARITH_RULE `1 <= SUC n`];
    MATCH_MP_TAC PERMUTES_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PERMUTES_SWAP THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`];
    REWRITE_TAC[o_THM; swap] THEN MESON_TAC[];
    ASM_REWRITE_TAC[o_THM; swap];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[o_THM; swap] THEN
    SUBGOAL_THEN `~((p:num->num) i = SUC n) /\ ~(p i = p(SUC n))`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[PERMUTES_INJECTIVE]]);;

let REARRANGEMENT_SUM_LE = prove
 (`!n (f:num->real->real) b p.
        (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                   ==> f i y + f j x <= f i x + f j y) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> sum(1..n) (\i. f i (b(p i))) <= sum(1..n) (\i. f i (b i))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_NUMSEG_SWAP_TOP) THEN
  ABBREV_TAC `q = swap(SUC n,(p:num->num)(SUC n)) o p` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..SUC n) (\i. (f:num->real->real) i (b((q:num->num) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_TWO_POINTS THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `SUC n`] THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL;
                    ARITH_RULE `1 <= SUC n`] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LE_REFL]];
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`;
                    REAL_LE_RADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let PERMUTES_NUMSEG_REVERSE = prove
 (`!n. (\j. if 1 <= j /\ j <= n then (n + 1) - j else j) permutes 1..n`,
  GEN_TAC THEN
  SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let REARRANGEMENT_SUM_GE_REVERSE = prove
 (`!n (f:num->real->real) b p.
        (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                   ==> f i y + f j x <= f i x + f j y) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> sum(1..n) (\i. f i (b((n + 1) - i)))
            <= sum(1..n) (\i. f i (b(p i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `\i x. --((f:num->real->real) i (--x))`;
    `\j. --((b:num->real)((n + 1) - j))`;
    `(\j. if 1 <= j /\ j <= n then (n + 1) - j else j) o (p:num->num)`]
   REARRANGEMENT_SUM_LE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        SPECL [`i:num`; `j:num`; `--y:real`; `--x:real`]) THEN
      ASM_REWRITE_TAC[REAL_LE_NEG2] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_NEG2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC PERMUTES_COMPOSE THEN
      ASM_REWRITE_TAC[PERMUTES_NUMSEG_REVERSE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(x:real) = --a /\ y = --c ==> x <= y ==> c <= a`) THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN CONJ_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[o_THM; REAL_NEG_NEG] THEN
  SUBGOAL_THEN `1 <= (p:num->num) i /\ p i <= n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let EXCHANGE_OF_CONSECUTIVE = prove
 (`!n (f:num->real->real).
        (!i x y. 1 <= i /\ i < n /\ x <= y
                 ==> f (i + 1) x - f i x <= f (i + 1) y - f i y)
        ==> !i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                      ==> f i y + f j x <= f i x + f j y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i = SUC j` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[ADD1] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let REARRANGEMENT_INEQUALITY = prove
 (`!n (a:num->real) b p.
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> a i <= a j) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> sum(1..n) (\i. a i * b(p i)) <= sum(1..n) (\i. a i * b i) /\
            sum(1..n) (\i. a i * b((n + 1) - i))
            <= sum(1..n) (\i. a i * b(p i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
              ==> (\i x. (a:num->real) i * x) i y + (\i x. a i * x) j x
                  <= (\i x. a i * x) i x + (\i x. a i * x) j y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (aj - ai) * (y - x) ==> ai * y + aj * x <= ai * x + aj * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_SUB_LE] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `\i x. (a:num->real) i * x`; `b:num->real`;
                   `p:num->num`] REARRANGEMENT_SUM_LE);
    MP_TAC(ISPECL [`n:num`; `\i x. (a:num->real) i * x`; `b:num->real`;
                   `p:num->num`] REARRANGEMENT_SUM_GE_REVERSE)] THEN
  ASM_REWRITE_TAC[]);;

let REARRANGEMENT_INEQUALITY_GEN = prove
 (`!n (f:num->real->real) b p.
        (!i x y. 1 <= i /\ i < n /\ x <= y
                 ==> f (i + 1) x - f i x <= f (i + 1) y - f i y) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> sum(1..n) (\i. f i (b(p i))) <= sum(1..n) (\i. f i (b i)) /\
            sum(1..n) (\i. f i (b((n + 1) - i)))
            <= sum(1..n) (\i. f i (b(p i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP EXCHANGE_OF_CONSECUTIVE) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REARRANGEMENT_SUM_LE;
    MATCH_MP_TAC REARRANGEMENT_SUM_GE_REVERSE] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The rearrangement inequality for products: if a_i, b_i >= 0 are both      *)
(* nondecreasing, then                                                       *)
(* prod (a_i + b_i) <= prod (a_i + b_{p(i)}) <= prod (a_i + b_{n+1-i}).      *)
(* Products of nonnegative factors f i (b j) under the exchange condition    *)
(* f i x f j y <= f i y f j x (i <= j, x <= y) are smallest for the sorted   *)
(* pairing and largest for the reversed one; the reversed exchange           *)
(* condition gives the sorted pairing as the largest.                        *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_LE_TWO_POINTS = prove
 (`!s (g:A->real) h k l.
        FINITE s /\ k IN s /\ l IN s /\ (!i. i IN s ==> &0 <= g i) /\
        (!i. i IN s /\ ~(i = k) /\ ~(i = l) ==> g i = h i) /\
        (k = l ==> g l = h l) /\ g k * g l <= h k * h l
        ==> product s g <= product s h`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:A = l` THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->real`; `s DELETE (k:A)`; `l:A`] PRODUCT_DELETE) THEN
  MP_TAC(ISPECL [`h:A->real`; `s DELETE (k:A)`; `l:A`] PRODUCT_DELETE) THEN
  MP_TAC(ISPECL [`g:A->real`; `s:A->bool`; `k:A`] PRODUCT_DELETE) THEN
  MP_TAC(ISPECL [`h:A->real`; `s:A->bool`; `k:A`] PRODUCT_DELETE) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  SUBGOAL_THEN
   `product ((s DELETE k) DELETE l) (g:A->real) =
    product ((s DELETE k) DELETE l) h`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product ((s DELETE k) DELETE l) (g:A->real)` MP_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[]);;

let REARRANGEMENT_PRODUCT_GE = prove
 (`!n (f:num->real->real) b p.
        (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> &0 <= f i (b j)) /\
        (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                   ==> f i x * f j y <= f i y * f j x) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> product(1..n) (\i. f i (b i)) <= product(1..n) (\i. f i (b(p i)))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; REAL_LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_NUMSEG_SWAP_TOP) THEN
  ABBREV_TAC `q = swap(SUC n,(p:num->num)(SUC n)) o p` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `product(1..SUC n) (\i. (f:num->real->real) i (b((q:num->num) i)))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PRODUCT_LE_TWO_POINTS THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `SUC n`] THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL;
                  ARITH_RULE `1 <= SUC n`] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_REFL]]);;

let REARRANGEMENT_PRODUCT_LE = prove
 (`!n (f:num->real->real) b p.
        (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> &0 <= f i (b j)) /\
        (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                   ==> f i y * f j x <= f i x * f j y) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> product(1..n) (\i. f i (b(p i))) <= product(1..n) (\i. f i (b i))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; REAL_LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_NUMSEG_SWAP_TOP) THEN
  ABBREV_TAC `q = swap(SUC n,(p:num->num)(SUC n)) o p` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `product(1..SUC n) (\i. (f:num->real->real) i (b((q:num->num) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_TWO_POINTS THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `SUC n`] THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL;
                    ARITH_RULE `1 <= SUC n`] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN
      ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LE_REFL]];
    ASM_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

let REARRANGEMENT_PRODUCT_LE_REVERSE = prove
 (`!n (f:num->real->real) b p.
        (!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> &0 <= f i (b j)) /\
        (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
                   ==> f i x * f j y <= f i y * f j x) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> product(1..n) (\i. f i (b(p i)))
            <= product(1..n) (\i. f i (b((n + 1) - i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `\i x. (f:num->real->real) i (--x)`;
    `\j. --((b:num->real)((n + 1) - j))`;
    `(\j. if 1 <= j /\ j <= n then (n + 1) - j else j) o (p:num->num)`]
   REARRANGEMENT_PRODUCT_LE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_NEG_NEG] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o
        SPECL [`i:num`; `j:num`; `--y:real`; `--x:real`]) THEN
      ASM_REWRITE_TAC[REAL_LE_NEG2];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_NEG2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC PERMUTES_COMPOSE THEN
      ASM_REWRITE_TAC[PERMUTES_NUMSEG_REVERSE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) = a /\ y = c ==> x <= y ==> a <= c`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[o_THM; REAL_NEG_NEG] THEN
  SUBGOAL_THEN `1 <= (p:num->num) i /\ p i <= n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let REARRANGEMENT_INEQUALITY_PRODUCT = prove
 (`!n (a:num->real) b p.
        (!i. 1 <= i /\ i <= n ==> &0 <= a i /\ &0 <= b i) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> a i <= a j) /\
        (!i j. 1 <= i /\ i <= j /\ j <= n ==> b i <= b j) /\
        p permutes 1..n
        ==> product(1..n) (\i. a i + b i)
            <= product(1..n) (\i. a i + b(p i)) /\
            product(1..n) (\i. a i + b(p i))
            <= product(1..n) (\i. a i + b((n + 1) - i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
           ==> &0 <= (\i x. (a:num->real) i + x) i (b j)) /\
    (!i j x y. 1 <= i /\ i <= j /\ j <= n /\ x <= y
               ==> (\i x. (a:num->real) i + x) i x * (\i x. a i + x) j y
                   <= (\i x. a i + x) i y * (\i x. a i + x) j x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= (aj - ai) * (y - x)
        ==> (ai + x) * (aj + y) <= (ai + y) * (aj + x)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_SUB_LE] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `\i x. (a:num->real) i + x`; `b:num->real`;
                   `p:num->num`] REARRANGEMENT_PRODUCT_GE);
    MP_TAC(ISPECL [`n:num`; `\i x. (a:num->real) i + x`; `b:num->real`;
                   `p:num->num`] REARRANGEMENT_PRODUCT_LE_REVERSE)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* For |a_i|, |b_i| <= 1, |prod a_i - prod b_i| <= sum |a_i - b_i|.          *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ABS_SUB_LE = prove
 (`!s (a:A->real) b.
        FINITE s /\ (!i. i IN s ==> abs(a i) <= &1 /\ abs(b i) <= &1)
        ==> abs(product s a - product s b) <= sum s (\i. abs(a i - b i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(product s (b:A->real)) <= &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN MATCH_MP_TAC PRODUCT_LE_1 THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `abs((a:A->real) x) * abs(product s a - product s b) +
    abs(a x - b x) * abs(product s b)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y + z ==> abs x <= abs y + abs z`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `abs(product s (a:A->real) - product s b)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL] THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* The AM-GM inequality over any finite index set (for s = {} both sides are *)
(* 1), by induction on s. The step x m^n <= ((n m + x) / (n + 1))^(n + 1)    *)
(* for m, x >= 0 is Bernoulli's inequality for (y / m)^(n + 1), y the mean.  *)
(* ------------------------------------------------------------------------- *)

let REAL_MUL_POW_LE_MEAN_POW = prove
 (`!n m x. &0 <= m /\ &0 <= x
           ==> x * m pow n <= ((&n * m + x) / (&n + &1)) pow (n + 1)`,
  let bernoulli = prove
   (`!h n. -- &1 <= h ==> &1 + &n * h <= (&1 + h) pow n`,
    GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[real_pow; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
    TRANS_TAC REAL_LE_TRANS `(&1 + h) * (&1 + &n * h)` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= &n * h * h
        ==> &1 + (&n + &1) * h <= (&1 + h) * (&1 + &n * h)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_SQUARE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_SIMP_TAC[real_pow; REAL_POW_ZERO; REAL_MUL_RZERO; REAL_MUL_LZERO;
                 ADD_CLAUSES; REAL_ADD_LID; REAL_DIV_1; REAL_POW_1;
                 REAL_MUL_RID; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `y = (&n * m + x) / (&n + &1)` THEN
  SUBGOAL_THEN `(&n + &1) * y = &n * m + x` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y / m - &1`; `n + 1`] bernoulli) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (y / m - &1) = y / m`; REAL_POW_DIV;
              GSYM REAL_OF_NUM_ADD] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH `-- &1 <= a - &1 <=> &0 <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (&n + &1) * (y / m - &1) = x / m` SUBST1_TAC THENL
   [UNDISCH_TAC `(&n + &1) * y = &n * m + x` THEN UNDISCH_TAC `&0 < m` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= c ==> b <= c`) THEN
  REWRITE_TAC[GSYM ADD1; real_pow] THEN UNDISCH_TAC `&0 < m` THEN
  CONV_TAC REAL_FIELD);;

let AGM_FINITE = prove
 (`!s (a:A->real).
     FINITE s /\ (!i. i IN s ==> &0 <= a i)
     ==> product s a <= (sum s a / &(CARD s)) pow (CARD s)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow; REAL_LE_REFL];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; CARD_CLAUSES; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `(a:A->real) x * (sum s a / &(CARD(s:A->bool))) pow CARD s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(s:A->bool)) * sum s a / &(CARD s) = sum s (a:A->real)`
  MP_TAC THENL
   [ASM_CASES_TAC `CARD(s:A->bool) = 0` THENL
     [SUBGOAL_THEN `s:A->bool = {}` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[CARD_EQ_0];
        REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES; REAL_MUL_LZERO]];
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(s:A->bool)`; `sum s (a:A->real) / &(CARD(s:A->bool))`;
                 `(a:A->real) x`] REAL_MUL_POW_LE_MEAN_POW) THEN
  ASM_SIMP_TAC[REAL_LE_DIV; SUM_POS_LE; REAL_POS] THEN
  DISCH_THEN(fun th -> DISCH_THEN(fun eq -> MP_TAC(REWRITE_RULE[eq] th))) THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD; REAL_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* For a_i > 0 with prod a_i >= 1 and t > 0, prod (t + a_i) >= (t + 1)^n.    *)
(* With u the mean of t / (t + a_i), the AM-GM inequality for t / (t + a_i)  *)
(* and for a_i / (t + a_i), whose means are u and 1 - u, gives the two       *)
(* hypotheses of the lemma.                                                  *)
(* ------------------------------------------------------------------------- *)

let SUM_PRODUCT_2_LEMMA = prove
 (`!n t q p u.
        ~(n = 0) /\ &0 < t /\ &0 < q /\ &1 <= p /\ &0 <= u /\ u <= &1 /\
        t pow n <= q * u pow n /\ p <= q * (&1 - u) pow n
        ==> (t + &1) pow n <= q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t <= (t + &1) * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_MUL;
                 REAL_ARITH `&0 < t ==> &0 <= t + &1`] THEN
    TRANS_TAC REAL_LE_TRANS `(q:real) * u pow n` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `u = &1` THENL
   [UNDISCH_TAC `p <= q * (&1 - u) pow n` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_POW_ZERO; REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < (t + &1) * (&1 - u)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_POW_MUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS `q * (&1 - u) pow n` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PRODUCT_ADD_POW_LE = prove
 (`!n (a:num->real) t.
        (!i. 1 <= i /\ i <= n ==> &0 < a i) /\ &1 <= product(1..n) a /\ &0 < t
        ==> (t + &1) pow n <= product(1..n) (\i. t + a i)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_pow; PRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n /\ 1 <= n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= n ==> &0 < t + (a:num->real) i`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_PRODUCT_2_LEMMA THEN
  MAP_EVERY EXISTS_TAC
   [`product(1..n) (a:num->real)`;
    `sum(1..n) (\i. t / (t + (a:num->real) i)) / &n`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[PRODUCT_POS_LT_NUMSEG] THEN
  SUBGOAL_THEN `&0 < product(1..n) (\i. t + (a:num->real) i)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRODUCT_POS_LT_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. (a:num->real) i / (t + a i)) / &n =
    &1 - sum(1..n) (\i. t / (t + a i)) / &n`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `sum(1..n) (\i. (a:num->real) i / (t + a i)) =
      sum(1..n) (\i. &1 - t / (t + a i))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_FIELD
        `&0 < t + a ==> a / (t + a) = &1 - t / (t + a)`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID] THEN
    UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    TRANS_TAC REAL_LE_TRANS `sum(1..n) (\i. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LE_ADDR;
                   REAL_LT_IMP_LE];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID; REAL_LE_REFL]];
    MP_TAC(ISPECL [`1..n`; `\i. t / (t + (a:num->real) i)`] AGM_FINITE) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; PRODUCT_DIV_NUMSEG;
                 PRODUCT_CONST_NUMSEG; ADD_SUB; REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC];
    MP_TAC(ISPECL [`1..n`; `\i. (a:num->real) i / (t + a i)`] AGM_FINITE) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; PRODUCT_DIV_NUMSEG;
                 REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* The first part of Chong's inequality: for a_i > 0 and a permutation p of  *)
(* 1..n, sum a_i / a_{p(i)} >= n.                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_RATIO_PERMUTE_GE = prove
 (`!n (a:num->real) p.
        p permutes 1..n /\ (!i. 1 <= i /\ i <= n ==> &0 < a i)
        ==> &n <= sum(1..n) (\i. a i / a(p i))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_LE_REFL]; STRIP_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= n ==> &0 < (a:num->real)(p i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..n`; `\i. (a:num->real) i / a(p i)`] AGM_FINITE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `product(1..n) (\i. (a:num->real) i / a(p i)) = &1`
  SUBST1_TAC THENL
   [REWRITE_TAC[PRODUCT_DIV_NUMSEG] THEN
    MP_TAC(ISPECL [`a:num->real`; `p:num->num`; `1..n`]
      (MATCH_MP ITERATE_PERMUTE MONOIDAL_REAL_MUL)) THEN
    ASM_REWRITE_TAC[GSYM product; o_DEF] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_DIV_REFL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_POW_1_LT THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* The cases n = 3 and n = 4 of Shapiro's inequality: for x_i > 0, with      *)
(* indices taken cyclically, sum x_i / (x_{i+1} + x_{i+2}) >= n / 2.         *)
(* Shapiro's inequality holds for even n <= 12 and odd n <= 23; only n = 3   *)
(* and n = 4 are proved here. For n = 3 the sum is Nesbitt's sum; for n = 4  *)
(* it follows from the Engel form of Cauchy-Schwarz with weights             *)
(* x_i (x_{i+1} + x_{i+2}).                                                  *)
(* ------------------------------------------------------------------------- *)

let CYCLIC_RATIO_SUM_3_GE = prove
 (`!x:num->real.
        &0 < x 1 /\ &0 < x 2 /\ &0 < x 3
        ==> &3 / &2 <= x 1 / (x 2 + x 3) + x 2 / (x 3 + x 1) +
                        x 3 / (x 1 + x 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `x:num->real`] NESBITT_INEQUALITY) THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`;
              TAUT `(p \/ q \/ r ==> s) <=>
                    (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  SIMP_TAC[SUM_CLAUSES_RIGHT; SUM_SING_NUMSEG; ARITH] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_LID;
              REAL_ARITH `(((a:real) + b) + c) - a = b + c /\
                          ((a + b) + c) - b = c + a /\
                          ((a + b) + c) - c = a + b`] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ADD_ASSOC]]);;

let CYCLIC_RATIO_SUM_4_GE = prove
 (`!x:num->real.
        &0 < x 1 /\ &0 < x 2 /\ &0 < x 3 /\ &0 < x 4
        ==> &2 <= x 1 / (x 2 + x 3) + x 2 / (x 3 + x 4) +
                  x 3 / (x 4 + x 1) + x 4 / (x 1 + x 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`1..4`;
    `\i. (x:num->real) i *
         (x(if i + 1 > 4 then (i + 1) - 4 else i + 1) +
          x(if i + 2 > 4 then (i + 2) - 4 else i + 2))`;
    `x:num->real`] SUM_SQUARE_LE_SUM_DIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG;
                ARITH_RULE `1 <= i /\ i <= 4 <=>
                            i = 1 \/ i = 2 \/ i = 3 \/ i = 4`] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> &0 <= a /\ (a = &0 ==> b = &0)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[prove
   (`!f. sum(1..4) f = f 1 + f 2 + f 3 + f 4`,
    GEN_TAC THEN SIMP_TAC[SUM_CLAUSES_RIGHT; ARITH] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN REAL_ARITH_TAC)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < x ==> x pow 2 / (x * y) = x / y`] THEN
  ABBREV_TAC
   `t = (x:num->real) 1 / (x 2 + x 3) + x 2 / (x 3 + x 4) +
        x 3 / (x 4 + x 1) + x 4 / (x 1 + x 2)` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `(x:num->real) 1 * (x 2 + x 3) + x 2 * (x 3 + x 4) +
              x 3 * (x 4 + x 1) + x 4 * (x 1 + x 2)` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_ADD];
    MP_TAC(SPEC `(x:num->real) 1 - x 3` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(x:num->real) 2 - x 4` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC]);;
