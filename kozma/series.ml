(* ========================================================================= *)
(* Series inequalities (Mathieu, Hilbert, Hardy), from L. Kozma, "Useful     *)
(* Inequalities" (v0.44).                                                    *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;
needs "kozma/means.ml";;

(* ------------------------------------------------------------------------- *)
(* Mathieu's inequality: 1/(c^2 + 1/2) < sum_(n>=1) 2n/(n^2 + c^2)^2 < 1/c^2 *)
(* for c <> 0, by telescoping bounds on each term.                           *)
(* ------------------------------------------------------------------------- *)

let MATHIEU_TERM_BOUNDS = prove
 (`!c n. 1 <= n
         ==> inv(&n pow 2 - &n + c pow 2 + inv(&2)) -
             inv(&(n + 1) pow 2 - &(n + 1) + c pow 2 + inv(&2)) <
             &2 * &n / (&n pow 2 + c pow 2) pow 2 /\
             (~(c = &0)
              ==> &2 * &n / (&n pow 2 + c pow 2) pow 2 <
                  inv(&n pow 2 - &n + c pow 2) -
                  inv(&(n + 1) pow 2 - &(n + 1) + c pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1 <= &n` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SPEC_TAC(`&n`,`x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (x:real) pow 2 - x /\ &0 <= (c:real) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(x:real) pow 2 - x = x * (x - &1)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `&0 < (x:real) pow 2 - x + c pow 2 + inv(&2) /\
      &0 < (x + &1) pow 2 - (x + &1) + c pow 2 + inv(&2) /\
      &0 < x pow 2 + c pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
      SUBGOAL_THEN `((x:real) + &1) pow 2 - (x + &1) = (x pow 2 - x) + &2 * x`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    SUBGOAL_THEN
     `&2 * x / ((x:real) pow 2 + c pow 2) pow 2 -
      (inv(x pow 2 - x + c pow 2 + inv(&2)) -
       inv((x + &1) pow 2 - (x + &1) + c pow 2 + inv(&2))) =
      &2 * x * (c pow 2 + inv(&4)) /
      ((x pow 2 + c pow 2) pow 2 * (x pow 2 - x + c pow 2 + inv(&2)) *
       ((x + &1) pow 2 - (x + &1) + c pow 2 + inv(&2)))`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`&0 < (x:real) pow 2 - x + c pow 2 + inv(&2)`;
        `&0 < ((x:real) + &1) pow 2 - (x + &1) + c pow 2 + inv(&2)`;
        `&0 < (x:real) pow 2 + c pow 2`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REPEAT((MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LT_DIV) THEN
           CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `&0 < (c:real) pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (x:real) pow 2 - x + c pow 2 /\
    &0 < (x + &1) pow 2 - (x + &1) + c pow 2 /\ &0 < x pow 2 + c pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    SUBGOAL_THEN `((x:real) + &1) pow 2 - (x + &1) = (x pow 2 - x) + &2 * x`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  SUBGOAL_THEN
   `(inv((x:real) pow 2 - x + c pow 2) -
     inv((x + &1) pow 2 - (x + &1) + c pow 2)) -
    &2 * x / (x pow 2 + c pow 2) pow 2 =
    &2 * x * x pow 2 /
    ((x pow 2 + c pow 2) pow 2 * (x pow 2 - x + c pow 2) *
     ((x + &1) pow 2 - (x + &1) + c pow 2))`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&0 < (x:real) pow 2 - x + c pow 2`;
      `&0 < ((x:real) + &1) pow 2 - (x + &1) + c pow 2`;
      `&0 < (x:real) pow 2 + c pow 2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT((MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LT_DIV) THEN
         CONJ_TAC) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC);;

let MATHIEU_SUMMABLE = prove
 (`!c. real_summable (from 1) (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n. &2 * inv(&n rpow &3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN MATCH_MP_TAC REAL_SUMMABLE_ZETA THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[IN_FROM; RPOW_POW] THEN
  STRIP_TAC THEN SUBGOAL_THEN `&1 <= &n` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SPEC_TAC(`&n`,`x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 < (x:real) pow 2 + c pow 2 /\ x pow 2 <= x pow 2 + c pow 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&1 <= (x:real) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * x / ((x:real) pow 2 + c pow 2) pow 2`
  (fun th -> REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 <= a ==> abs a = a`) th])
  THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 < (x:real) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
  SUBGOAL_THEN `(x:real) * x pow 3 = (x pow 2) pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_POW_2]]);;

let MATHIEU_INEQUALITY_LOWER = prove
 (`!c. real_summable (from 1) (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2) /\
       &1 / (c pow 2 + &1 / &2) <
       real_infsum (from 1) (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[MATHIEU_SUMMABLE] THEN
  MP_TAC(SPEC `c:real` MATHIEU_SUMMABLE) THEN
  ABBREV_TAC `f = \n. &2 * &n / (&n pow 2 + c pow 2) pow 2` THEN
  DISCH_TAC THEN
  ABBREV_TAC `L = \n. inv(&n pow 2 - &n + c pow 2 + inv(&2))` THEN
  SUBGOAL_THEN `!n. &0 <= (f:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MP_TAC(SPEC `&n` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. 1 <= n ==> (L:num->real) n - L(n + 1) < f n`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["L"; "f"] THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[MATHIEU_TERM_BOUNDS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!N. 1 <= N ==> (L:num->real)(N + 1) <= inv(&N)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&1 <= &N` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `&N` REAL_LE_POW_2) THEN
    SPEC_TAC(`&N`,`x:real`) THEN GEN_TAC THEN
    SUBGOAL_THEN `((x:real) + &1) pow 2 - (x + &1) = x pow 2 + x`
    SUBST1_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = (f:num->real) 1 - ((L:num->real) 1 - L 2)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
      can (find_term ((=) `(<):real->real->bool`)) (concl th) &&
      is_forall(concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:num->real`; `from 1`; `N + 1`]
                REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  ASM_REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `1 <= N + 1`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(2..N+1) (\n. (L:num->real) n - L(n + 1)) <= sum(2..N+1) f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(2..N+1) (\n. (L:num->real) n - L(n + 1)) = L 2 - L((N + 1) + 1)`
  SUBST_ALL_TAC THENL
   [SUBGOAL_THEN
     `sum(2..N+1) (\n. (L:num->real) n - L(n + 1)) =
      --(sum(2..N+1) (\n. L(n + 1) - L n))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_DIFFS_ALT] THEN COND_CASES_TAC THENL
       [REAL_ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `N + 1` o check (fun th ->
    can (find_term ((=) `inv:real->real`)) (concl th) &&
    is_forall(concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `inv(&(N + 1)) <= inv(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / (c pow 2 + &1 / &2) = (L:num->real) 1` SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MATHIEU_INEQUALITY = prove
 (`!c. ~(c = &0)
       ==> real_summable (from 1)
             (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2) /\
           &1 / (c pow 2 + &1 / &2) <
           real_infsum (from 1)
             (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2) /\
           real_infsum (from 1)
             (\n. &2 * &n / (&n pow 2 + c pow 2) pow 2) <
           &1 / c pow 2`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATHIEU_INEQUALITY_LOWER] THEN
  ABBREV_TAC `f = \n. &2 * &n / (&n pow 2 + c pow 2) pow 2` THEN
  ABBREV_TAC `U = \n. inv(&n pow 2 - &n + c pow 2)` THEN
  SUBGOAL_THEN `!n. &0 <= (f:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MP_TAC(SPEC `&n` REAL_LE_POW_2) THEN
      MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. 1 <= n ==> (f:num->real) n < U n - U(n + 1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["U"; "f"] THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[MATHIEU_TERM_BOUNDS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (U:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "U" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    SUBGOAL_THEN `&0 < c pow 2 /\ &0 <= &n pow 2 - &n` MP_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE];
        SUBGOAL_THEN `&n pow 2 - &n = &n * (&n - &1)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `n = 0` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS; REAL_SUB_LE; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real`; `1`; `(f:num->real) 1 + (U:num->real) 2`]
                REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH `(y:real) <= b ==> a + y <= a + b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(2..m) (\n. (U:num->real) n - U(n + 1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum(2..m) (\n. (U:num->real) n - U(n + 1)) =
      --(sum(2..m) (\n. U(n + 1) - U n))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_DIFFS_ALT] THEN COND_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < b ==> --(b - a) <= a`) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_NEG_0; REAL_LT_IMP_LE]]];
    STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th ->
    can (find_term ((=) `(<):real->real->bool`)) (concl th) &&
    is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `&1 / c pow 2 = (U:num->real) 1` SUBST1_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Schur test for a symmetric nonnegative kernel K with weights          *)
(* sqrt(i/j), and the passage from the finite rectangular bound to the       *)
(* iterated series.                                                          *)
(* ------------------------------------------------------------------------- *)

let SCHUR_TEST_FINITE = prove
 (`!K C (a:num->real) (b:num->real) m n.
     (!i j. 1 <= i /\ 1 <= j ==> &0 <= K i j) /\
     (!i j. 1 <= i /\ 1 <= j ==> K i j = K j i) /\
     (!i N. 1 <= i ==> sum(1..N) (\j. K i j * sqrt(&i / &j)) <= C)
     ==> sum(1..m) (\i. sum(1..n) (\j. abs(a i * b j) * K i j)) <=
         C * sqrt(sum(1..m) (\i. a i pow 2)) *
         sqrt(sum(1..n) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kpos")
   (CONJUNCTS_THEN2 (LABEL_TAC "ksym") (LABEL_TAC "row"))) THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [USE_THEN "row" (MP_TAC o SPECL [`1`; `0`]) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i N. 1 <= i
          ==> sum(1..N) (\j. (K:num->num->real) i j * inv(sqrt(&j))) <=
              C * inv(sqrt(&i))`
  (LABEL_TAC "row'") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&i)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "row" (MP_TAC o SPECL [`i:num`; `N:num`]) THEN
    ASM_SIMP_TAC[SQRT_DIV; REAL_POS; real_div; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(k:real) * s * t = s * (k * t)`] THEN
    REWRITE_TAC[SUM_LMUL] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:num->num->real`; `\i:num. inv(sqrt(&i))`;
                 `\j:num. inv(sqrt(&j))`; `1..m`; `1..n`; `C:real`; `C:real`;
                 `a:num->real`; `b:num->real`] SCHUR_TEST) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS
     `sum(1..m) (\i. (K:num->num->real) j i * inv(sqrt(&i)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      USE_THEN "ksym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "row'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Tonelli for nonnegative double series: if all rectangular partial sums    *)
(* are bounded by B, every row and column is summable, both iterated series  *)
(* converge, they have the same sum, and that sum is at most B.              *)
(* ------------------------------------------------------------------------- *)

let REAL_SERIES_TONELLI = prove
 (`!(f:num->num->real) k l B.
     (!i j. k <= i /\ l <= j ==> &0 <= f i j) /\
     (!m n. sum(k..m) (\i. sum(l..n) (\j. f i j)) <= B)
     ==> (!i. k <= i ==> real_summable (from l) (\j. f i j)) /\
         (!j. l <= j ==> real_summable (from k) (\i. f i j)) /\
         real_summable (from k) (\i. real_infsum (from l) (\j. f i j)) /\
         real_summable (from l) (\j. real_infsum (from k) (\i. f i j)) /\
         real_infsum (from l) (\j. real_infsum (from k) (\i. f i j)) =
         real_infsum (from k) (\i. real_infsum (from l) (\j. f i j)) /\
         real_infsum (from k) (\i. real_infsum (from l) (\j. f i j)) <= B`,
  SUBGOAL_THEN
   `!(g:num->num->real) k l B.
      (!i j. k <= i /\ l <= j ==> &0 <= g i j) /\
      (!m n. sum(k..m) (\i. sum(l..n) (\j. g i j)) <= B)
      ==> (!i. k <= i ==> real_summable (from l) (\j. g i j)) /\
          real_summable (from k) (\i. real_infsum (from l) (\j. g i j)) /\
          real_infsum (from k) (\i. real_infsum (from l) (\j. g i j)) <= B`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!i. k <= i ==> real_summable (from l) (\j. (g:num->num->real) i j) /\
                     real_infsum (from l) (\j. g i j) <= B`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS THEN
      ASM_SIMP_TAC[] THEN X_GEN_TAC `n:num` THEN
      TRANS_TAC REAL_LE_TRANS
       `sum(k..i) (\i'. sum(l..n) (\j. (g:num->num->real) i' j))` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`{i:num}`; `k..i`;
                     `\i'. sum(l..n) (\j. (g:num->num->real) i' j)`]
                    SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; IN_DIFF;
                  IN_SING; ETA_AX] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THEN
      MAP_EVERY EXISTS_TAC [`\j. (g:num->num->real) n j`; `from l`] THEN
      ASM_SIMP_TAC[REAL_SUMS_INFSUM; IN_FROM];
      ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC
     `\n. sum(k..m) (\i. sum(l..n) (\j. (g:num->num->real) i j))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\i n. sum(l..n) (\j. (g:num->num->real) i j)`;
                   `\i. real_infsum (from l) (\j. (g:num->num->real) i j)`;
                   `k..m`] REALLIM_SUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
    ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun one ->
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:num->num->real`; `k:num`; `l:num`; `B:real`] one) THEN
    MP_TAC(ISPECL [`\j i. (f:num->num->real) i j`; `l:num`; `k:num`; `B:real`]
                  one) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
     [GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SUM_SWAP_NUMSEG] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(!i. k <= i
           ==> &0 <= real_infsum (from l) (\j. (f:num->num->real) i j)) /\
      (!j. l <= j
           ==> &0 <= real_infsum (from k) (\i. (f:num->num->real) i j))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THENL
       [MAP_EVERY EXISTS_TAC [`\j. (f:num->num->real) i j`; `from l`];
        MAP_EVERY EXISTS_TAC [`\i. (f:num->num->real) i j`; `from k`]] THEN
      ASM_SIMP_TAC[REAL_SUMS_INFSUM; IN_FROM];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\j i. (f:num->num->real) i j`; `l:num`; `k:num`;
                     `real_infsum (from k)
                        (\i. real_infsum (from l)
                               (\j. (f:num->num->real) i j))`]
                    one);
      MP_TAC(ISPECL [`f:num->num->real`; `k:num`; `l:num`;
                     `real_infsum (from l)
                        (\j. real_infsum (from k)
                               (\i. (f:num->num->real) i j))`]
                    one)] THEN
    REWRITE_TAC[] THEN (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN
    CONJ_TAC THEN TRY(ASM_SIMP_TAC[] THEN NO_TAC) THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SUM_SWAP_NUMSEG] THENL
     [TRANS_TAC REAL_LE_TRANS
       `sum(k..n) (\i. real_infsum (from l)
                         (\j. (f:num->num->real) i j))`;
      TRANS_TAC REAL_LE_TRANS
       `sum(l..n) (\j. real_infsum (from k)
                         (\i. (f:num->num->real) i j))`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[];
       ALL_TAC] THEN
     MATCH_MP_TAC REAL_PARTIAL_SUMS_LE_INFSUM_GEN THEN
     ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_FROM])));;

let ITERATED_SERIES_BOUND = prove
 (`!K C (a:num->real) (b:num->real).
     (!i j. 1 <= i /\ 1 <= j ==> &0 <= K i j) /\
     (!m n. sum(1..m) (\i. sum(1..n) (\j. abs(a i * b j) * K i j)) <=
            C * sqrt(sum(1..m) (\i. a i pow 2)) *
            sqrt(sum(1..n) (\j. b j pow 2))) /\
     real_summable (from 1) (\i. a i pow 2) /\
     real_summable (from 1) (\j. b j pow 2)
     ==> (!i. 1 <= i ==> real_summable (from 1) (\j. a i * b j * K i j)) /\
         real_summable (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j * K i j)) /\
         real_infsum (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j * K i j)) <=
         C * sqrt(real_infsum (from 1) (\i. a i pow 2)) *
         sqrt(real_infsum (from 1) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!f:num->real n. real_summable (from 1) (\i. f i pow 2)
                    ==> sum(1..n) (\i. f i pow 2) <=
                        real_infsum (from 1) (\i. f i pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\i. (f:num->real) i pow 2`; `from 1`; `n:num`]
                  REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    ASM_REWRITE_TAC[FROM_INTER_NUMSEG; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C * sqrt(real_infsum (from 1) (\i. (a:num->real) i pow 2)) *
        sqrt(real_infsum (from 1) (\j. (b:num->real) j pow 2)) =
    max C (&0) * sqrt(real_infsum (from 1) (\i. a i pow 2)) *
        sqrt(real_infsum (from 1) (\j. b j pow 2))`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `&0 <= C` THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= C ==> max C (&0) = C`]; ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(real_infsum (from 1) (\i. (a:num->real) i pow 2)) *
      sqrt(real_infsum (from 1) (\j. (b:num->real) j pow 2)) = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    SUBGOAL_THEN
     `!m n. sum(1..m) (\i. (a:num->real) i pow 2) *
            sum(1..n) (\j. (b:num->real) j pow 2) = &0`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`] o check (fun th ->
        free_in `C:real` (concl th) && is_forall (concl th))) THEN
      SUBGOAL_THEN
       `&0 <= sum(1..m)
                (\i. sum(1..n) (\j. abs((a:num->real) i * b j) * K i j))`
      MP_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_ABS_POS];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&0 <= sum(1..m) (\i. (a:num->real) i pow 2) *
              sum(1..n) (\j. (b:num->real) j pow 2)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN
      SPEC_TAC(`sum(1..m) (\i. (a:num->real) i pow 2) *
                sum(1..n) (\j. (b:num->real) j pow 2)`,`P:real`) THEN
      GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= --C * sqrt P` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `C * sqrt P = &0` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ENTIRE; SQRT_EQ_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SQRT_MUL; SQRT_EQ_0] THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\n. sum(1..n) (\i. (a:num->real) i pow 2) *
                    sum(1..n) (\j. (b:num->real) j pow 2)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_MUL THEN
      REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REALLIM_CONST]];
    ALL_TAC] THEN
  ABBREV_TAC
   `M = max C (&0) *
        sqrt(real_infsum (from 1) (\i. (a:num->real) i pow 2)) *
        sqrt(real_infsum (from 1) (\j. (b:num->real) j pow 2))` THEN
  SUBGOAL_THEN
   `!m n. sum(1..m)
            (\i. sum(1..n) (\j. abs((a:num->real) i * b j) * K i j)) <= M`
  (LABEL_TAC "P") THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`] o check (fun th ->
      free_in `C:real` (concl th) && is_forall (concl th))) THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z:real. y <= z ==> x <= y ==> x <= z`) THEN
    EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `max C (&0) * sqrt(sum(1..m) (\i. (a:num->real) i pow 2)) *
      sqrt(sum(1..n) (\j. (b:num->real) j pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC) THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\i j. abs((a:num->real) i * (b:num->real) j) * (K:num->num->real) i j`;
    `1`; `1`; `M:real`] REAL_SERIES_TONELLI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_ABS_POS];
      USE_THEN "P" (fun th -> REWRITE_TAC[th])];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ 1 <= j
          ==> abs((a:num->real) i * (b:num->real) j * K i j) =
              abs(a i * b j) * K i j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[REAL_ABS_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i ==> real_summable (from 1)
                     (\j. (a:num->real) i * (b:num->real) j * K i j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\j:num. abs((a:num->real) i * (b:num->real) j) *
                        (K:num->num->real) i j` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_FROM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC
   `y = \i. real_infsum (from 1)
              (\j. abs((a:num->real) i * (b:num->real) j) *
                   (K:num->num->real) i j)` THEN
  ABBREV_TAC
   `x = \i. real_infsum (from 1)
              (\j. (a:num->real) i * (b:num->real) j *
                   (K:num->num->real) i j)` THEN
  SUBGOAL_THEN
   `!i. 1 <= i
        ==> ((\j. (a:num->real) i * (b:num->real) j * K i j) real_sums x i)
              (from 1) /\
            ((\j. abs(a i * b j) * K i j) real_sums y i) (from 1)`
  (LABEL_TAC "S") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
    REWRITE_TAC[REAL_SUMS_INFSUM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i ==> abs((x:num->real) i) <= y i`
  (LABEL_TAC "R") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "S"
     (STRIP_ASSUME_TAC o C MP (ASSUME `1 <= i`) o SPEC `i:num`) THEN
    MATCH_MP_TAC
     (REAL_ARITH `!u v:real. u <= v /\ --v <= u ==> abs u <= v`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_LE THEN
      MAP_EVERY EXISTS_TAC
       [`\j. (a:num->real) i * (b:num->real) j * K i j`;
        `\j. abs((a:num->real) i * (b:num->real) j) * K i j`;
        `from 1`] THEN
      ASM_REWRITE_TAC[IN_FROM] THEN
      ASM_MESON_TAC[REAL_ABS_LE];
      MATCH_MP_TAC REAL_SERIES_LE THEN
      MAP_EVERY EXISTS_TAC
       [`\j. --(abs((a:num->real) i * (b:num->real) j) * K i j)`;
        `\j. (a:num->real) i * (b:num->real) j * K i j`;
        `from 1`] THEN
      ASM_SIMP_TAC[REAL_SERIES_NEG; IN_FROM] THEN
      ASM_MESON_TAC[REAL_ARITH `!x:real. --abs x <= x`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_summable (from 1) (y:num->real) /\ real_infsum (from 1) y <= M`
  STRIP_ASSUME_TAC THENL
   [(ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
    (EXPAND_TAC "y" THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 1) (x:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN EXISTS_TAC `y:num->real` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `1` THEN REWRITE_TAC[IN_FROM] THEN
    REPEAT STRIP_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_infsum (from 1) (y:num->real)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SERIES_LE THEN
  MAP_EVERY EXISTS_TAC [`x:num->real`; `y:num->real`; `from 1`] THEN
  ASM_REWRITE_TAC[REAL_SUMS_INFSUM; IN_FROM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!u v:real. abs u <= v ==> u <= v`) THEN
  USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SQUARE_SUMMABLE_DIV_SUMMABLE = prove
 (`!b:num->real. real_summable (from 1) (\j. b j pow 2)
                 ==> real_summable (from 1) (\j. b j / &j)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\j. abs((b:num->real) j * inv(&j))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_ABS_MUL_SQUARES THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_INV; GSYM RPOW_POW] THEN
    MATCH_MP_TAC REAL_SUMMABLE_ZETA THEN REAL_ARITH_TAC;
    EXISTS_TAC `1` THEN REWRITE_TAC[real_div; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Hilbert's inequality with kernel 1/max(i,j) and constant 4: the weight    *)
(* sums are at most 2 + 2, by comparison with the integrals of x^(-1/2) and  *)
(* x^(-3/2).                                                                 *)
(* ------------------------------------------------------------------------- *)

let SUM_INV_SQRT_LE = prove
 (`!n. sum(1..n) (\j. inv(sqrt(&j))) <= &2 * sqrt(&n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; SQRT_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
  REWRITE_TAC[SQRT_1; REAL_INV_1] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[SQRT_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[SUM_TRIV_NUMSEG; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. inv(sqrt x)`; `\x. &2 * sqrt x`; `2`; `n:num`]
                REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; SQRT_1] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REAL_DIFF_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_INV_MUL]] THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!s a. s <= a - &2 * &1 ==> &1 + s <= a`) THEN
    FIRST_X_ASSUM ACCEPT_TAC]);;

let SUM_INV_MUL_SQRT_LE = prove
 (`!m d. 1 <= m
         ==> sum(m + 1..m + d) (\j. inv(&j * sqrt(&j))) <=
             &2 * (inv(sqrt(&m)) - inv(sqrt(&(m + d))))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_SIMP_TAC[ADD_CLAUSES; SUM_TRIV_NUMSEG; ARITH_RULE `m < m + 1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. inv(x * sqrt x)`; `\x. --(&2 * inv(sqrt x))`;
                 `m + 1`; `m + d:num`]
                REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(m + &1) - &1 = m`;
              IN_REAL_INTERVAL] THEN
  SUBGOAL_THEN `&1 <= &m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REAL_DIFF_TAC THEN
      SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt x /\ sqrt x pow 2 = x` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < x`; `&0 < sqrt x`; `sqrt x pow 2 = x`] THEN
      CONV_TAC REAL_FIELD;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      SUBGOAL_THEN `&0 < x /\ &0 < sqrt x /\ sqrt x <= sqrt y`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s a b. s <= --(&2 * b) - --(&2 * a) ==> s <= &2 * (a - b)`) THEN
    FIRST_X_ASSUM ACCEPT_TAC]);;

let HILBERT_MAX_WEIGHT_BOUND = prove
 (`!i N. sum(1..N) (\j. inv(&(MAX i j)) * sqrt(&i / &j)) <= &4`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; SQRT_0; REAL_MUL_RZERO;
                    SUM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f = \j. inv(&(MAX i j)) * sqrt(&i / &j)` THEN
  SUBGOAL_THEN `!j. &0 <= (f:num->real) j` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS; SQRT_POS_LE; REAL_LE_DIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&i) /\ sqrt(&i) pow 2 = &i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..i) f + sum(i + 1..N) f` THEN CONJ_TAC THENL
   [ASM_CASES_TAC `(i:num) <= N` THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG;
                 ARITH_RULE `~((i:num) <= N) ==> N < i + 1`] THEN
    MP_TAC(ISPECL [`f:num->real`; `1`; `N:num`; `i:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH `!x y:real. &0 <= y ==> x <= (x + y) + &0`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y:real. x <= &2 /\ y <= &2 ==> x + y <= &4`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(sqrt(&i)) * sum(1..i) (\j. inv(sqrt(&j)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `MAX i j = i` SUBST1_TAC THENL
       [REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[SQRT_DIV; REAL_POS] THEN
      SUBGOAL_THEN `&0 < sqrt(&j)` MP_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&i)`; `sqrt(&i) pow 2 = &i`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(sqrt(&i)) * &2 * sqrt(&i)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[SUM_INV_SQRT_LE; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      UNDISCH_TAC `&0 < sqrt(&i)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_CASES_TAC `(i:num) <= N` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_TRIV_NUMSEG;
                 ARITH_RULE `~((i:num) <= N) ==> N < i + 1`] THEN
    REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&i) * sum(i + 1..i + d) (\j. inv(&j * sqrt(&j)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `MAX i j = j` SUBST1_TAC THENL
     [REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SQRT_DIV; REAL_POS] THEN
    SUBGOAL_THEN `&0 < sqrt(&j) /\ sqrt(&j) pow 2 = &j` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_POS] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&i) * &2 * (inv(sqrt(&i)) - inv(sqrt(&(i + d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[SUM_INV_MUL_SQRT_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&i) * inv(sqrt(&(i + d)))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[SQRT_POS_LE; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&i) * &2 * (inv(sqrt(&i)) - inv(sqrt(&(i + d)))) =
    &2 - &2 * (sqrt(&i) * inv(sqrt(&(i + d))))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&i)` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let HILBERT_MAX_INEQUALITY_ABS_FINITE = prove
 (`!(a:num->real) (b:num->real) m n.
     sum(1..m) (\i. sum(1..n) (\j. abs(a i * b j) / &(MAX i j))) <=
     &4 * sqrt(sum(1..m) (\i. a i pow 2)) * sqrt(sum(1..n) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  MP_TAC(ISPECL [`\i j. inv(&(MAX i j))`; `&4`; `a:num->real`; `b:num->real`;
                 `m:num`; `n:num`] SCHUR_TEST_FINITE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; HILBERT_MAX_WEIGHT_BOUND] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let HILBERT_MAX_INEQUALITY_FINITE = prove
 (`!(a:num->real) (b:num->real) m n.
     sum(1..m) (\i. sum(1..n) (\j. a i * b j / &(MAX i j))) <=
     &4 * sqrt(sum(1..m) (\i. a i pow 2)) * sqrt(sum(1..n) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..m)
      (\i. sum(1..n) (\j. abs((a:num->real) i * b j) / &(MAX i j)))` THEN
  REWRITE_TAC[HILBERT_MAX_INEQUALITY_ABS_FINITE] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_ABS_LE; REAL_LE_INV_EQ; REAL_POS]);;

let HILBERT_MAX_INEQUALITY = prove
 (`!(a:num->real) (b:num->real).
     real_summable (from 1) (\i. a i pow 2) /\
     real_summable (from 1) (\j. b j pow 2)
     ==> (!i. real_summable (from 1) (\j. a i * b j / &(MAX i j))) /\
         real_summable (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j / &(MAX i j))) /\
         real_infsum (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j / &(MAX i j))) <=
         &4 * sqrt(real_infsum (from 1) (\i. a i pow 2)) *
         sqrt(real_infsum (from 1) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\i j. inv(&(MAX i j))`; `&4`; `a:num->real`; `b:num->real`]
                ITERATED_SERIES_BOUND) THEN
  REWRITE_TAC[GSYM real_div] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[HILBERT_MAX_INEQUALITY_ABS_FINITE; REAL_LE_INV_EQ;
                    REAL_POS];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `MAX 0 j = j`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC SQUARE_SUMMABLE_DIV_SUMMABLE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hilbert's inequality with kernel 1/(i+j) and constant pi: the weight sums *)
(* are at most 2 atn(sqrt(N/i)) < pi.                                        *)
(* ------------------------------------------------------------------------- *)

let HILBERT_WEIGHT_BOUND = prove
 (`!i N. sum(1..N) (\j. inv(&(i + j)) * sqrt(&i / &j)) <= pi`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; SQRT_0; REAL_MUL_RZERO;
                    SUM_0] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&0 < &i /\ &0 < sqrt(&i) /\ sqrt(&i) pow 2 = &i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THENL
     [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC SQRT_POW_2] THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `N:num = 0` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `~(N = 0) ==> 1 <= N`] THEN
  REWRITE_TAC[ARITH] THEN
  SUBGOAL_THEN
   `inv(&i + &1) * sqrt(&i / &1) <= &2 * atn(sqrt(&1 / &i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_DIV_1; real_div; REAL_MUL_LID; SQRT_INV] THEN
    MP_TAC(SPEC `inv(sqrt(&i))` ATN_GE_DIV) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN
     `inv(&i + &1) * sqrt(&i) = inv(sqrt(&i)) / (&1 + inv(sqrt(&i)) pow 2)`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < sqrt(&i)`; `sqrt(&i) pow 2 = &i`] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv(sqrt(&i)) / (&1 + inv(sqrt(&i)) pow 2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MP_TAC(SPEC `inv(sqrt(&i))` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(2..N) (\j. inv(&i + &j) * sqrt(&i / &j)) <=
    &2 * atn(sqrt(&N / &i)) - &2 * atn(sqrt(&1 / &i))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `N:num = 1` THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[SUM_TRIV_NUMSEG; ARITH; REAL_SUB_REFL; REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. inv(&i + x) * sqrt(&i / x)`;
                   `\x. &2 * atn(sqrt(x / &i))`; `2`; `N:num`]
                  REAL_SUM_INTEGRAL_UBOUND_DECREASING) THEN
    REWRITE_TAC[REAL_ARITH `&2 - &1 = &1`] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\x. &2 * atn(sqrt(x / &i))) has_real_derivative f')
         (atreal x)`)) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_DIV; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `&0 < sqrt x /\ sqrt x pow 2 = x` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < sqrt x`; `sqrt x pow 2 = x`; `&0 < x`;
        `&0 < sqrt(&i)`; `sqrt(&i) pow 2 = &i`; `&0 < &i`] THEN
      CONV_TAC REAL_FIELD;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[real_div] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(&N / &i)` ATN_BOUNDS) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let HILBERT_INEQUALITY_ABS_FINITE = prove
 (`!(a:num->real) (b:num->real) m n.
     sum(1..m) (\i. sum(1..n) (\j. abs(a i * b j) / &(i + j))) <=
     pi * sqrt(sum(1..m) (\i. a i pow 2)) * sqrt(sum(1..n) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div] THEN
  MP_TAC(ISPECL [`\i j. inv(&(i + j))`; `pi`; `a:num->real`; `b:num->real`;
                 `m:num`; `n:num`] SCHUR_TEST_FINITE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS; HILBERT_WEIGHT_BOUND] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let HILBERT_INEQUALITY_FINITE = prove
 (`!(a:num->real) (b:num->real) m n.
     sum(1..m) (\i. sum(1..n) (\j. a i * b j / &(i + j))) <=
     pi * sqrt(sum(1..m) (\i. a i pow 2)) * sqrt(sum(1..n) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..m) (\i. sum(1..n) (\j. abs((a:num->real) i * b j) / &(i + j)))` THEN
  REWRITE_TAC[HILBERT_INEQUALITY_ABS_FINITE] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_ABS_LE; REAL_LE_INV_EQ; REAL_POS]);;

let HILBERT_INEQUALITY = prove
 (`!(a:num->real) (b:num->real).
     real_summable (from 1) (\i. a i pow 2) /\
     real_summable (from 1) (\j. b j pow 2)
     ==> (!i. real_summable (from 1) (\j. a i * b j / &(i + j))) /\
         real_summable (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j / &(i + j))) /\
         real_infsum (from 1)
           (\i. real_infsum (from 1) (\j. a i * b j / &(i + j))) <=
         pi * sqrt(real_infsum (from 1) (\i. a i pow 2)) *
         sqrt(real_infsum (from 1) (\j. b j pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\i j. inv(&(i + j))`; `pi`; `a:num->real`; `b:num->real`]
                ITERATED_SERIES_BOUND) THEN
  REWRITE_TAC[GSYM real_div] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[HILBERT_INEQUALITY_ABS_FINITE; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC SQUARE_SUMMABLE_DIV_SUMMABLE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hardy's inequality: sum_k (A_k/k)^p <= (p/(p-1))^p sum_k a_k^p for p > 1  *)
(* and a >= 0, with A_k = a_1 + ... + a_k (Elliott's proof).                 *)
(* ------------------------------------------------------------------------- *)

let HARDY_STEP = prove
 (`!p k x y.
     &1 < p /\ &1 <= k /\ &0 <= x /\ &0 <= y
     ==> x rpow p - p / (p - &1) * x rpow (p - &1) * (k * x - (k - &1) * y)
         <= ((k - &1) * y rpow p - k * x rpow p) / (p - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x rpow (p - &1) * x = x rpow p` ASSUME_TAC THENL
   [ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_RZERO; RPOW_ZERO] THEN
      COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real`; `p - &1`; `&1`] RPOW_ADD) THEN
    ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_ARITH `p - &1 + &1 = p`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x rpow (p - &1)`; `y:real`; `p / (p - &1)`; `p:real`]
                YOUNG_INEQUALITY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_RPOW] THEN
  SUBGOAL_THEN `(p - &1) * p / (p - &1) = p` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `X = x rpow p` THEN ABBREV_TAC `Z = x rpow (p - &1)` THEN
  ABBREV_TAC `W = y rpow p` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `p / (p - &1) * Z * (k * x - (k - &1) * y) =
    (p / (p - &1) * k) * (Z * x) - (p / (p - &1) * (k - &1)) * (Z * y)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(X - (p / (p - &1) * k) * X) +
              (p / (p - &1) * (k - &1)) * (X / (p / (p - &1)) + W / p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!a b c d:real. c <= d ==> a - (b - c) <= (a - b) + d`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 < p` THEN
    CONV_TAC REAL_FIELD]);;

let HARDY_TELESCOPE = prove
 (`!(a:num->real) p n.
     &1 < p /\ (!i. 1 <= i /\ i <= n ==> &0 <= a i)
     ==> sum(1..n) (\k. (sum(1..k) a / &k) rpow p -
                        p / (p - &1) * (sum(1..k) a / &k) rpow (p - &1) * a k)
         <= --(&n * (sum(1..n) a / &n) rpow p) / (p - &1)`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `!k. &k * (sum(1..k) (a:num->real) / &k) = sum(1..k) a`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `k:num = 0` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_LZERO; REAL_NEG_0;
                real_div; REAL_LE_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
  MP_TAC(ISPECL [`p:real`; `&(SUC n)`;
                 `sum(1..SUC n) (a:num->real) / &(SUC n)`;
                 `sum(1..n) (a:num->real) / &n`] HARDY_STEP) THEN
  SUBGOAL_THEN `&(SUC n) - &1 = &n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= SUC n`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..SUC n) a - sum(1..n) a = (a:num->real) (SUC n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let HARDY_INEQUALITY_FINITE = prove
 (`!(a:num->real) p n.
     &1 < p /\ (!i. 1 <= i /\ i <= n ==> &0 <= a i)
     ==> sum(1..n) (\k. (sum(1..k) a / &k) rpow p) <=
         (p / (p - &1)) rpow p * sum(1..n) (\k. a k rpow p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= n ==> &0 <= sum(1..k) (a:num->real) / &k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = sum(1..n) (\k. (sum(1..k) (a:num->real) / &k) rpow p)` THEN
  ABBREV_TAC `A = sum(1..n) (\k. (a:num->real) k rpow p)` THEN
  ABBREV_TAC `q = p / (p - &1)` THEN
  SUBGOAL_THEN `&0 < q /\ &0 <= S /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "S"; "A"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `B = sum(1..n)
          (\k. (sum(1..k) (a:num->real) / &k) rpow (p - &1) * a k)` THEN
  SUBGOAL_THEN `(S:real) <= q * B` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:num->real`; `p:real`; `n:num`] HARDY_TELESCOPE) THEN
    ASM_REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL] THEN
    SUBGOAL_THEN `&0 <= &n * (sum(1..n) (a:num->real) / &n) rpow p / (p - &1)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[LE_REFL];
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1..n`; `\k. (sum(1..k) (a:num->real) / &k) rpow (p - &1)`;
                 `a:num->real`; `q:real`; `p:real`]
                HOELDER_SUM_INEQUALITY) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "q" THEN UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..n)
      (\i. abs((sum(1..i) (a:num->real) / &i) rpow (p - &1) * a i)) = B /\
    sum(1..n)
      (\i. abs((sum(1..i) (a:num->real) / &i) rpow (p - &1)) rpow q) = S /\
    sum(1..n) (\i. abs((a:num->real) i) rpow p) = A`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["B"; "S"; "A"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    (SUBGOAL_THEN `&0 <= sum(1..i) (a:num->real) / &i /\ &0 <= a i`
     STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
    ASM_SIMP_TAC[REAL_ARITH `!x:real. &0 <= x ==> abs x = x`; RPOW_POS_LE;
                 REAL_LE_MUL; RPOW_RPOW] THEN
    AP_TERM_TAC THEN EXPAND_TAC "q" THEN
    UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `S = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= x ==> x rpow &1 = x` ASSUME_TAC THENL
   [REWRITE_TAC[RPOW_POW; REAL_POW_1]; ALL_TAC] THEN
  SUBGOAL_THEN `S rpow (&1 / p) * S rpow (&1 / q) = S` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
    SUBGOAL_THEN `&1 / p + &1 / q = &1` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `S rpow (&1 / p) <= q * A rpow (&1 / p)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `S rpow (&1 / q)` THEN
    ASM_SIMP_TAC[RPOW_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q * (B:real)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `q * S rpow (&1 / q) * A rpow (&1 / p)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `S = (S rpow (&1 / p)) rpow p /\
                A = ((A:real) rpow (&1 / p)) rpow p`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&1 / p * p = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RPOW_MUL] THEN MATCH_MP_TAC RPOW_LE2 THEN
  ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let HARDY_INEQUALITY = prove
 (`!(a:num->real) p.
     &1 < p /\ (!i. 1 <= i ==> &0 <= a i) /\
     real_summable (from 1) (\k. a k rpow p)
     ==> real_summable (from 1) (\k. (sum(1..k) a / &k) rpow p) /\
         real_infsum (from 1) (\k. (sum(1..k) a / &k) rpow p) <=
         (p / (p - &1)) rpow p * real_infsum (from 1) (\k. a k rpow p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SUMMABLE_POS_BOUNDED_PARTIAL_SUMS THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(p / (p - &1)) rpow p * sum(1..n) (\k. (a:num->real) k rpow p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HARDY_INEQUALITY_FINITE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. (a:num->real) k rpow p`; `from 1`; `n:num`]
                REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  ASM_REWRITE_TAC[FROM_INTER_NUMSEG; IN_FROM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_SIMP_TAC[]);;
