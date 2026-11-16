(* ========================================================================= *)
(* Matrix inequalities: Hadamard's inequality and Schur's inequality for the *)
(* diagonal of a real symmetric matrix, from L. Kozma, "Useful Inequalities" *)
(* (v0.44).                                                                  *)
(* ========================================================================= *)

needs "Multivariate/topology.ml";;

let HADAMARD_INEQUALITY = prove
 (`!A:real^N^N.
     det A pow 2 <=
     product (1..dimindex(:N)) (\i. sum (1..dimindex(:N)) (\j. A$i$j pow 2))`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `product (1..dimindex(:N))
      (\i. sum (1..dimindex(:N)) (\j. (A:real^N^N)$i$j pow 2)) =
    product (1..dimindex(:N)) (\i. norm(row i A)) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM PRODUCT_MUL_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_2; NORM_POW_2; dot] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[row; LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product(1..dimindex(:N)) (\i. norm(row i (A:real^N^N)))` THEN
    REWRITE_TAC[HADAMARD_INEQUALITY_ROW] THEN REAL_ARITH_TAC]);;

let SUM_UNIT_WEIGHTS_LE_PREFIX = prove
 (`!(l:num->real) w c n k.
     k <= n /\
     (!j. 1 <= j /\ j <= n ==> &0 <= w j /\ w j <= &1) /\
     sum(1..n) w = &k /\
     (!j. 1 <= j /\ j <= k ==> c <= l j) /\
     (!j. k + 1 <= j /\ j <= n ==> l j <= c)
     ==> sum(1..n) (\j. w j * l j) <= sum(1..k) l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "w")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lo")
      (LABEL_TAC "hi"))))) THEN
  SUBGOAL_THEN `!f. sum(1..n) f = sum(1..k) f + sum(k+1..n) f`
   (fun th -> ONCE_REWRITE_TAC[th] THEN MP_TAC(SPEC `w:num->real` th))
  THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_COMBINE_R THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..k) (\j. (&1 - w j) * c) <=
    sum(1..k) (\j. (&1 - w j) * (l:num->real) j)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SUBGOAL_THEN `&0 <= (w:num->real) i /\ w i <= &1` MP_TAC THENL
     [USE_THEN "w" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c <= (l:num->real) i` MP_TAC THENL
     [USE_THEN "lo" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(k+1..n) (\j. w j * (l:num->real) j) <= sum(k+1..n) (\j. w j * c)`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SUBGOAL_THEN `&0 <= (w:num->real) i /\ w i <= &1` MP_TAC THENL
     [USE_THEN "w" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(l:num->real) i <= c` MP_TAC THENL
     [USE_THEN "hi" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG; SUM_RMUL; REAL_MUL_LID;
              SUM_CONST_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) - 1 = k`; SUB_0] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `&k:real` then SUBST1_TAC th
    else NO_TAC) THEN
  REAL_ARITH_TAC);;

let DIAGONALIZATION_DIAGONAL_ENTRY = prove
 (`!A:real^N^N P:real^N^N l i.
    orthogonal_matrix P /\
    transp P ** A ** P = (lambda i j. if i = j then l i else &0) /\
    1 <= i /\ i <= dimindex(:N)
    ==> A$i$i = sum (1..dimindex(:N)) (\j. P$i$j pow 2 * l j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^N^N)
    = (P:real^N^N) ** (transp P ** A ** P) ** transp P`
  SUBST1_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; transp] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
  SUBGOAL_THEN
   `sum (1..dimindex(:N))
      (\k. if j = k then (l:num->real) k * (P:real^N^N)$i$k else &0) =
    sum (1..dimindex(:N)) (\k. if k = j then l j * P$i$j else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING]);;

let ORTHOGONAL_MATRIX_SUM_SQUARES = prove
 (`!P:real^N^N.
    orthogonal_matrix P
    ==> (!j. 1 <= j /\ j <= dimindex(:N)
             ==> sum (1..dimindex(:N)) (\i. P$i$j pow 2) = &1) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> sum (1..dimindex(:N)) (\j. P$i$j pow 2) = &1)`,
  GEN_TAC THEN REWRITE_TAC[orthogonal_matrix] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c") (LABEL_TAC "r")) THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THENL
   [USE_THEN "c" (MP_TAC o AP_TERM `\M:real^N^N. M$k$k`);
    USE_THEN "r" (MP_TAC o AP_TERM `\M:real^N^N. M$k$k`)] THEN
  SIMP_TAC[matrix_mul; transp; mat; LAMBDA_BETA; REAL_POW_2;
           ASSUME `1 <= k`; ASSUME `k <= dimindex(:N)`] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[LAMBDA_BETA; ASSUME `1 <= k`; ASSUME `k <= dimindex(:N)`]);;

let SCHUR_DIAGONAL_INEQUALITY_GEN = prove
 (`!A:real^N^N P:real^N^N l s.
    orthogonal_matrix P /\
    transp P ** A ** P = (lambda i j. if i = j then l i else &0) /\
    (!i j. 1 <= i /\ i <= j /\ j <= dimindex(:N) ==> l j <= l i) /\
    s SUBSET 1..dimindex(:N)
    ==> sum s (\i. A$i$i) <= sum (1..CARD s) l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (s:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  MP_TAC(ISPEC `P:real^N^N` ORTHOGONAL_MATRIX_SUM_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "col") (LABEL_TAC "row")) THEN
  SUBGOAL_THEN
   `sum s (\i. (A:real^N^N)$i$i) =
    sum (1..dimindex(:N)) (\j. sum s (\i. (P:real^N^N)$i$j pow 2) * l j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum s (\i. sum (1..dimindex(:N))
                     (\j. (P:real^N^N)$i$j pow 2 * l j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC DIAGONALIZATION_DIAGONAL_ENTRY THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN_NUMSEG];
      REWRITE_TAC[GSYM SUM_RMUL] THEN
      MP_TAC(ISPECL [`\i j. (P:real^N^N)$i$j pow 2 * (l:num->real) j`;
                     `s:num->bool`; `1..dimindex(:N)`] SUM_SWAP) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_UNIT_WEIGHTS_LE_PREFIX THEN
  EXISTS_TAC `(l:num->real) (MAX 1 (CARD(s:num->bool)))` THEN
  MP_TAC(ISPECL [`s:num->bool`; `1..dimindex(:N)`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_POW_2] THEN
    USE_THEN "col" (fun th -> GEN_REWRITE_TAC RAND_CONV
      [GSYM(MATCH_MP th (CONJ (ASSUME `1 <= j`)
                              (ASSUME `j <= dimindex(:N)`)))]) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_LE_POW_2];
    MP_TAC(ISPECL [`\i j. (P:real^N^N)$i$j pow 2`; `s:num->bool`;
                   `1..dimindex(:N)`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum (s:num->bool) (\i. &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      BETA_TAC THEN USE_THEN "row" MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET; IN_NUMSEG];
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]];
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC]);;

let SCHUR_DIAGONAL_INEQUALITY = prove
 (`!A:real^N^N P:real^N^N l d k.
    orthogonal_matrix P /\
    transp P ** A ** P = (lambda i j. if i = j then l i else &0) /\
    (!i j. 1 <= i /\ i <= j /\ j <= dimindex(:N) ==> l j <= l i) /\
    (?r. r permutes 1..dimindex(:N) /\
         !i. 1 <= i /\ i <= dimindex(:N) ==> d i = A$(r i)$(r i)) /\
    k <= dimindex(:N)
    ==> sum (1..k) d <= sum (1..k) l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `P:real^N^N`; `l:num->real`;
                 `IMAGE (r:num->num) (1..k)`]
    SCHUR_DIAGONAL_INEQUALITY_GEN) THEN
  SUBGOAL_THEN
   `!x y. x IN 1..k /\ y IN 1..k /\ (r:num->num) x = r y ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SUM_IMAGE th]) THEN
  SUBGOAL_THEN `CARD(IMAGE (r:num->num) (1..k)) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `CARD(1..k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
      REWRITE_TAC[CARD_NUMSEG_1]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:num->num) x IN 1..dimindex(:N)` MP_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_TRANS];
      REWRITE_TAC[IN_NUMSEG]];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= c ==> a <= c:real`) THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let DIAGONALIZATION_CHARACTERISTIC_POLYNOMIAL = prove
 (`!A:real^N^N P l.
    orthogonal_matrix P /\
    transp P ** A ** P = (lambda i j. if i = j then l i else &0)
    ==> !x. det(x %% mat 1 - A) = product (1..dimindex(:N)) (\i. x - l i)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D:real^N^N = lambda i j. if i = j then l i else &0` THEN
  SUBGOAL_THEN
   `x %% mat 1 - A:real^N^N = (P:real^N^N) ** (x %% mat 1 - D) ** transp P`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && is_comb(lhs(concl th)) &&
         fst(strip_comb(lhs(concl th))) =
         `( ** ):real^N^N->real^N^N->real^N^N`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_LMUL;
                MATRIX_MUL_RMUL; MATRIX_MUL_RID; MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 * y * &1 = y /\ --(&1) * y * --(&1) = y`] THEN
  (SUBGOAL_THEN `diagonal_matrix(x %% mat 1 - D:real^N^N)`
    (fun th -> REWRITE_TAC[MATCH_MP DET_DIAGONAL th]) THENL
    [EXPAND_TAC "D" THEN
     SIMP_TAC[diagonal_matrix; MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT;
              MAT_COMPONENT; LAMBDA_BETA] THEN
     SIMP_TAC[REAL_MUL_RZERO; REAL_SUB_REFL];
     MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN EXPAND_TAC "D" THEN
     SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT;
              LAMBDA_BETA; REAL_MUL_RID]]));;

let SYMMETRIC_MATRIX_DIAGONALIZABLE_SORTED = prove
 (`!A:real^N^N.
    symmetric_matrix A
    ==> ?P:real^N^N l.
          orthogonal_matrix P /\
          transp P ** A ** P = (lambda i j. if i = j then l i else &0) /\
          (!i j. 1 <= i /\ i <= j /\ j <= dimindex(:N) ==> l j <= l i)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `d:num->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\i j. (d:num->real) j < d i` TOPOLOGICAL_SORT) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)`; `1..dimindex(:N)`]) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1; REAL_NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. i IN 1..dimindex(:N) ==> (f:num->num) i IN 1..dimindex(:N)`
  (LABEL_TAC "rng") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N) /\
          (f:num->num) i = f j ==> i = j`
  (LABEL_TAC "inj") THENL
   [MP_TAC(ISPECL [`f:num->num`; `1..dimindex(:N)`] CARD_IMAGE_EQ_INJ) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `1..dimindex (:N) = IMAGE (f:num->num) (1..dimindex (:N))` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
  ABBREV_TAC `Q:real^N^N = lambda i j. (P:real^N^N)$i$(f j)` THEN
  SUBGOAL_THEN
   `!B:real^N^N j k.
      1 <= j /\ j <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
      ==> (transp (Q:real^N^N) ** B ** Q)$j$k =
          (transp (P:real^N^N) ** B ** P)$(f j)$(f k)`
  (LABEL_TAC "conj") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `1 <= (f:num->num) j /\ f j <= dimindex(:N) /\
      1 <= f k /\ f k <= dimindex(:N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN ASM_SIMP_TAC[matrix_mul; transp; LAMBDA_BETA] THEN
    EXPAND_TAC "Q" THEN
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rhs(concl th) = `Q:real^N^N` then ALL_TAC
      else NO_TAC) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k. 1 <= j /\ j <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
          ==> ((f:num->num) j = f k <=> j = k)`
  (LABEL_TAC "eqf") THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> 1 <= (f:num->num) j /\ f j <= dimindex(:N)`
  (LABEL_TAC "rng'") THENL [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Q:real^N^N`; `\i:num. (d:num->real) (f i)`] THEN
  REWRITE_TAC[orthogonal_matrix] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MESON[MATRIX_MUL_LID]
      `transp Q ** Q:real^N^N = transp Q ** mat 1 ** Q`] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    USE_THEN "conj" (fun th -> ASM_SIMP_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LID] THEN
    USE_THEN "rng'" (fun th -> MP_TAC(SPEC `j:num` th) THEN
                               MP_TAC(SPEC `k:num` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mat;
                                                              LAMBDA_BETA];
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `((P:real^N^N) ** transp P)$i$k = (mat 1:real^N^N)$i$k`
    MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_matrix]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Q" THEN ASM_SIMP_TAC[matrix_mul; transp; LAMBDA_BETA] THEN
    SUBGOAL_THEN
     `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> (Q:real^N^N)$a$b = (P:real^N^N)$a$(f b)`
    (LABEL_TAC "qc") THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN
      FIRST_X_ASSUM(fun th ->
        if is_eq(concl th) && rhs(concl th) = `Q:real^N^N` then ALL_TAC
        else NO_TAC) THEN
      ASM_SIMP_TAC[LAMBDA_BETA];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum (1..dimindex(:N)) (\x. (P:real^N^N)$i$(f x) * P$k$(f x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "qc" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->num`; `\m. (P:real^N^N)$i$m * P$k$m`;
                   `1..dimindex(:N)`] SUM_IMAGE) THEN
    ANTS_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `1..dimindex (:N) = IMAGE (f:num->num) (1..dimindex (:N))` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]);
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    USE_THEN "conj" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "rng'" (fun th -> MP_TAC(SPEC `j:num` th) THEN
                               MP_TAC(SPEC `k:num` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `i:num = j` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `d:num->real` (concl th) &&
      not(free_in `A:real^N^N` (concl th)))) THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC]);;
