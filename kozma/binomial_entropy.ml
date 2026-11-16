(* ========================================================================= *)
(* Binomial coefficients, Stirling's formula and the binary entropy, from    *)
(* L. Kozma, "Useful Inequalities" (v0.44).                                  *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Multivariate/realanalysis.ml";;
needs "Multivariate/gamma.ml";;
needs "kozma/combinatorics.ml";;
needs "kozma/means.ml";;

(* ------------------------------------------------------------------------- *)
(* Bounds on C(n,k): n^k/k^k, (n-k+1)^k/k! <= C(n,k) <= n^k/k! <= (en/k)^k   *)
(* and C(n,k) <= n^n/(k^k (n-k)^(n-k)), via k! C(n,k) = prod_i (n-i+1).      *)
(* ------------------------------------------------------------------------- *)

let BINOM_GE_POW_DIV_POW = prove
 (`!n k. k <= n ==> &n pow k / &k pow k <= &(binom(n,k))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[real_pow; binom; REAL_DIV_1; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(binom(n,k)) = product(1..k) (\i. (&n - &i + &1) / (&k - &i + &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[PRODUCT_DIV_NUMSEG; GSYM BINOM_FALLING_FACTORIAL] THEN
    MP_TAC(SPECL [`k:num`; `k:num`] BINOM_FALLING_FACTORIAL) THEN
    REWRITE_TAC[BINOM_REFL; REAL_MUL_RID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_FIELD `~(f = &0) ==> b = (f * b) / f`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_DIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < &k /\ &0 < &k - &i + &1 /\ &i <= &k /\ &k <= &n /\ &1 <= &i`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 < k - i + &1 <=> i < k + &1`;
                REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
               REAL_ARITH `(x:real) / y * z = (x * z) / y`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= (n - k) * (i - &1) ==> n * (k - i + &1) <= (n - i + &1) * k`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let BINOM_GE_SUB_POW_DIV_FACT = prove
 (`!n k. k <= n ==> (&n - &k + &1) pow k / &(FACT k) <= &(binom(n,k))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[BINOM_FALLING_FACTORIAL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&i <= &k /\ &k <= &n` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC]);;

let BINOM_LE_POW_DIV_FACT = prove
 (`!n k. &(binom(n,k)) <= &n pow k / &(FACT k)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[BINOM_FALLING_FACTORIAL] THEN
  ASM_CASES_TAC `k:num <= n` THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &i /\ &i <= &k /\ &k <= &n` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[GSYM BINOM_FALLING_FACTORIAL] THEN
    ASM_SIMP_TAC[BINOM_LT; ARITH_RULE `~(k:num <= n) ==> n < k`] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC REAL_POW_LE THEN
    REWRITE_TAC[REAL_POS]]);;

let POW_DIV_FACT_LE_EXP_POW = prove
 (`!x k. &0 <= x ==> x pow k / &(FACT k) <= (exp(&1) * x / &k) pow k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[real_pow; FACT; REAL_DIV_1; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `&k`] REAL_EXP_POW_FACT_LE) THEN
  ASM_SIMP_TAC[REAL_POS; LE_1] THEN
  SUBGOAL_THEN `exp(&k) = exp(&1) pow k` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_RID]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 < &k pow k /\ &0 < &(FACT k)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (x:real) pow k` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&k pow k / &(FACT k) + &1 <= exp (&1) pow k` THEN
  UNDISCH_TAC `&0 < &k pow k` THEN UNDISCH_TAC `&0 < &(FACT k)` THEN
  SPEC_TAC(`(x:real) pow k`, `X:real`) THEN
  SPEC_TAC(`&k pow k`, `Kp:real`) THEN
  SPEC_TAC(`&(FACT k)`, `G:real`) THEN SPEC_TAC(`exp(&1) pow k`, `E:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(Kp:real) <= E * G` ASSUME_TAC THENL
   [UNDISCH_TAC `Kp / G + &1 <= E` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ;
                 REAL_ARITH `Kp / G + &1 <= E <=> Kp / G <= E - &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `((E:real) * X / Kp) * G = (X * (E * G)) / Kp` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let BINOM_LE_ENTROPY_POW = prove
 (`!n k. k <= n
       ==> &(binom(n,k)) <= &n pow n / (&k pow k * &(n - k) pow (n - k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m. &0 < &m pow m` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[real_pow; REAL_LT_01] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
  SUBGOAL_THEN `&n = &k + &(n - k)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_BINOMIAL_THEOREM] THEN
  MP_TAC(ISPECL [`{k:num}`; `0..n`;
                 `\j. &(binom(n,j)) * &k pow j * &(n - k) pow (n - j)`]
         SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; SUM_SING; LE_0] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    REWRITE_TAC[REAL_MUL_AC]]);;

let BINOM_POWER_INEQUALITY = prove
 (`!n k. k <= n
       ==> max (&n pow k / &k pow k) ((&n - &k + &1) pow k / &(FACT k))
             <= &(binom(n,k)) /\
           &(binom(n,k)) <= &n pow k / &(FACT k) /\
           &n pow k / &(FACT k) <= (exp(&1) * &n / &k) pow k /\
           &(binom(n,k)) <= &n pow n / (&k pow k * &(n - k) pow (n - k))`,
  SIMP_TAC[REAL_MAX_LE; BINOM_GE_POW_DIV_POW; BINOM_GE_SUB_POW_DIV_FACT;
           BINOM_LE_POW_DIV_FACT; POW_DIV_FACT_LE_EXP_POW; REAL_POS;
           BINOM_LE_ENTROPY_POW]);;

(* ------------------------------------------------------------------------- *)
(* Products and scaling: C(n1,k1) C(n2,k2) <= C(n1+n2,k1+k2), and t^k C(n,k) *)
(* <= C(tn,k), from m^k C(n,k) <= n^k C(m,k) for n <= m.                     *)
(* ------------------------------------------------------------------------- *)

let BINOM_PRODUCT_INEQUALITY = prove
 (`!n1 n2 k1 k2. binom(n1,k1) * binom(n2,k2) <= binom(n1 + n2,k1 + k2)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[BINOM_0] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LE_REFL; LE_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `k2:num` num_CASES) THENL
   [REWRITE_TAC[binom; MULT_CLAUSES; ADD_CLAUSES] THEN
    TRANS_TAC LE_TRANS `binom(n1 + n2,k1)` THEN
    SIMP_TAC[BINOM_MONO; ARITH_RULE `n1 + n2 <= SUC(n1 + n2)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k1:num`; `0`]) THEN
    REWRITE_TAC[binom; MULT_CLAUSES; ADD_CLAUSES];
    REWRITE_TAC[ADD_CLAUSES; binom; LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[GSYM ADD_SUC]]);;

let BINOM_SCALING_INEQUALITY_GEN = prove
 (`!m n k. n <= m ==> m EXP k * binom(n,k) <= n EXP k * binom(m,k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:num <= n` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[BINOM_LT; ARITH_RULE `~(k:num <= n) ==> n < k`;
                 MULT_CLAUSES; LE_0]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&(FACT k)` THEN
  REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
  REWRITE_TAC[REAL_ARITH `(f:real) * a * b = a * f * b`] THEN
  REWRITE_TAC[BINOM_FALLING_FACTORIAL] THEN
  SUBGOAL_THEN
   `!a c. &(FACT k) * a * &(binom(c,k)) =
          a * product(1..k) (\i. &c - &i + &1)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM BINOM_FALLING_FACTORIAL; REAL_MUL_AC]; ALL_TAC] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o RAND_CONV)
   [GSYM CARD_NUMSEG_1] THEN
  SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG; GSYM PRODUCT_MUL_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &i /\ &i <= &k /\ &k <= &n /\ &n <= &m` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (m - n) * (i - &1) ==> m * (n - i + &1) <= n * (m - i + &1)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let BINOM_SCALING_INEQUALITY = prove
 (`!t n k. t EXP k * binom(n,k) <= binom(t * n,k)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; EXP_ZERO; BINOM_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[binom; MULT_CLAUSES; LE_REFL; LE_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; BINOM_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; LE_REFL; LE_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t * n:num`; `n:num`; `k:num`]
         BINOM_SCALING_INEQUALITY_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n <= t * n <=> 1 * n <= t * n`;
                LE_MULT_RCANCEL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MULT_EXP; GSYM MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Partial sums: sum_{i<=d} C(n,i) <= min{n^d + 1, (en/d)^d, 2^n}.           *)
(* ------------------------------------------------------------------------- *)

let SUM_BINOM_LE_POW_ADD_1 = prove
 (`!n d. sum(0..d) (\i. &(binom(n,i))) <= &n pow d + &1`,
  REWRITE_TAC[GSYM REAL_OF_NUM_SUM_NUMSEG; REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
              REAL_OF_NUM_LE; NSUM_BINOM_LE_POW]);;

let SUM_BINOM_LE_POW_2 = prove
 (`!n d. sum(0..d) (\i. &(binom(n,i))) <= &2 pow n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&2 pow n = sum(0..n) (\i. &(binom(n,i)))` SUBST1_TAC THENL
   [MP_TAC(SPECL [`n:num`; `&1`; `&1`] REAL_BINOMIAL_THEOREM) THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
    CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `d:num <= n` THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; REAL_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. d = n + p:num` (X_CHOOSE_THEN `p:num` SUBST1_TAC) THENL
   [EXISTS_TAC `d - n:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; LE_0; ARITH_RULE `0 <= n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `y = &0 ==> x + y <= x`) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; BINOM_EQ_0] THEN ASM_ARITH_TAC);;

let SUM_BINOM_LE_EXP_POW = prove
 (`!n d. d <= n
       ==> sum(0..d) (\i. &(binom(n,i))) <= (exp(&1) * &n / &d) pow d`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG; binom; real_pow; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &d /\ &0 < &n /\ &d <= &n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = &d / &n` THEN
  SUBGOAL_THEN `&0 < q /\ q <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow d * sum(0..d) (\i. &(binom(n,i))) <= exp(&d)`
  MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `sum(0..d) (\i. &(binom(n,i)) * q pow i)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..n) (\i. &(binom(n,i)) * q pow i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_REFL] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `q:real`; `&1`] REAL_BINOMIAL_THEOREM) THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`&d`; `&n`] RPOW_ADD_DIV_LE_EXP) THEN
    ASM_REWRITE_TAC[RPOW_POW] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_SYM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp(&1) * &n / &d = exp(&1) / q` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < &d` THEN UNDISCH_TAC `&0 < &n` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let BINOM_SUM_INEQUALITY = prove
 (`!n d. d <= n
       ==> sum(0..d) (\i. &(binom(n,i))) <= &n pow d + &1 /\
           sum(0..d) (\i. &(binom(n,i))) <= (exp(&1) * &n / &d) pow d /\
           sum(0..d) (\i. &(binom(n,i))) <= &2 pow n`,
  SIMP_TAC[SUM_BINOM_LE_POW_ADD_1; SUM_BINOM_LE_EXP_POW;
           SUM_BINOM_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* A lower bound: n^k/k! (1 - k(k-1)/(2n)) <= C(n,k), from prod (1 + d_i) >= *)
(* 1 + sum d_i; hence n^k/(4 k!) <= C(n,k) for k^2 <= n.                     *)
(* ------------------------------------------------------------------------- *)

let SUM_PRED_NUMSEG = prove
 (`!k. sum(1..k) (\i. &i - &1) = &k * (&k - &1) / &2`,
  INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`;
    ARITH_RULE `~(1 = 0)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let BINOM_SQRT_INEQUALITY_GEN = prove
 (`!n k. &n pow k / &(FACT k) * (&1 - &(k * (k - 1)) / (&2 * &n))
         <= &(binom(n,k))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0; REAL_SUB_RZERO;
                    REAL_MUL_RID; BINOM_0] THEN
    ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[real_pow; FACT; REAL_INV_1; REAL_MUL_RID;
                    REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_POW_ZERO; REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `k:num <= n + 1` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[BINOM_LT; ARITH_RULE `~(k:num <= n + 1) ==> n < k`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= --(&1 - x) <=> &1 <= x`] THEN
    SUBGOAL_THEN `&0 < &2 * &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    TRANS_TAC LE_TRANS `2 * k` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]] THEN
  SUBGOAL_THEN `&0 < &(FACT k)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) / f * y = (a * y) / f`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[BINOM_FALLING_FACTORIAL] THEN
  SUBGOAL_THEN `~(&n = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `product(1..k) (\i. &n - &i + &1) =
                product(1..k) (\i. &n * (&1 + (&1 - &i) / &n))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG; PRODUCT_CONST_NUMSEG_1] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MP_TAC(ISPECL [`1..k`; `\i. (&1 - &i) / &n`] PRODUCT_ONE_ADD_GE) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
   [DISJ2_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LNEG; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `--(n:real) <= &1 - i <=> i <= n + &1`;
                REAL_ARITH `&1 - (i:real) <= &0 <=> &1 <= i`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a:real) = --b ==> &1 + a <= p ==> &1 - b <= p`) THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (x:real) = --(x - &1)`; SUM_NEG;
              SUM_PRED_NUMSEG] THEN
  ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; REAL_NEG_0] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB;
               ARITH_RULE `~(k = 0) ==> 1 <= k`] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let BINOM_SQRT_INEQUALITY = prove
 (`!n k. k EXP 2 <= n ==> &n pow k / (&4 * &(FACT k)) <= &(binom(n,k))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `&n pow k / &(FACT k) * (&1 - &(k * (k - 1)) / (&2 * &n))` THEN
  REWRITE_TAC[BINOM_SQRT_INEQUALITY_GEN] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) * (b * c) = (a * c) * b`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  SUBGOAL_THEN `&(k * (k - 1)) * inv(&2) * inv(&n) <= inv(&2)` MP_TAC THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) * inv(&2) * b = inv(&2) * a * b`] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> inv(&2) * x <= inv(&2)`) THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 < &n` (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th]) THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE] THEN
  TRANS_TAC LE_TRANS `k EXP 2` THEN
  ASM_REWRITE_TAC[EXP_2; LE_MULT_LCANCEL] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Stirling: with the remainder                                              *)
(* r(n) = ln n! - ((n+1/2) ln n - n) - ln(2 pi)/2 (stirling_remainder), so   *)
(* that n! = sqrt(2 pi n) (n/e)^n e^r(n),                                    *)
(* r(n) - 1/(12n) increases and r(n) - 1/(12n+1) decreases, so r converges,  *)
(* and Wallis's product (library WALLIS) makes the limit 0. Hence the        *)
(* Robbins bounds 1/(12n+1) <= r(n) <= 1/(12n) for n >= 1, and              *)
(* n! / (sqrt(2 pi n) (n/e)^n) -> 1. The outer links to e(n/e)^n and         *)
(* en(n/e)^n hold for n >= 2 and fail at n = 1.                              *)
(* ------------------------------------------------------------------------- *)

let STIRLING_STEP_BOUNDS = prove
 (`!x. &1 <= x
       ==> &1 / (&12 * x + &1) - &1 / (&12 * x + &13)
             <= (x + &1 / &2) * log((x + &1) / x) - &1 /\
           (x + &1 / &2) * log((x + &1) / x) - &1
             <= &1 / (&12 * x) - &1 / (&12 * x + &12)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `&1 / (&2 * x + &1)` LOG_RATIO_ODD_BOUNDS) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ;
                   REAL_ARITH `&1 <= x ==> &0 < &2 * x + &1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &1 / (&2 * x + &1)) / (&1 - &1 / (&2 * x + &1)) =
                (x + &1) / x`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SPEC_TAC(`log((x + &1) / x)`, `l:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x + &1 / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `(x + &1 / &2) *
      (&2 * &1 / (&2 * x + &1) + &2 * (&1 / (&2 * x + &1)) pow 3 / &3) -
      &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC
       `(&24 * x - &23) /
        (&3 * (&2 * x + &1) pow 2 * (&12 * x + &1) * (&12 * x + &13))`
       (REAL_ARITH `!c a b:real. a - b = c /\ &0 <= c ==> b <= a`)) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&1 <= x` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - &1 <= b - &1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    TRANS_TAC REAL_LE_TRANS
     `(x + &1 / &2) *
      (&2 * &1 / (&2 * x + &1) +
       &2 * (&1 / (&2 * x + &1)) pow 3 /
       (&3 * (&1 - (&1 / (&2 * x + &1)) pow 2))) - &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - &1 <= b - &1`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `&1 - (&1 / (&2 * x + &1)) pow 2 =
                    &4 * x * (x + &1) / (&2 * x + &1) pow 2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&1 <= x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      UNDISCH_TAC `&1 <= x` THEN CONV_TAC REAL_FIELD]]);;

let stirling_remainder = new_definition
 `stirling_remainder n =
    log(&(FACT n)) - ((&n + &1 / &2) * log(&n) - &n) - log(&2 * pi) / &2`;;

let STIRLING_REMAINDER_STEP = prove
 (`!n. 1 <= n
       ==> stirling_remainder n - stirling_remainder(n + 1) =
           (&n + &1 / &2) * log(&(n + 1) / &n) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stirling_remainder] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &(SUC n) /\ &0 < &(FACT n)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_DIV] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC);;

let STIRLING_REMAINDER_STEP_MONO = prove
 (`!k. 1 <= k
       ==> stirling_remainder k - &1 / (&12 * &k) <=
           stirling_remainder(k + 1) - &1 / (&12 * &(k + 1)) /\
           stirling_remainder(k + 1) - &1 / (&12 * &(k + 1) + &1) <=
           stirling_remainder k - &1 / (&12 * &k + &1)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `k:num` STIRLING_REMAINDER_STEP) THEN
  MP_TAC(SPEC `&k` STIRLING_STEP_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`(&k + &1 / &2) * log((&k + &1) / &k)`, `q:real`) THEN
  REWRITE_TAC[REAL_ARITH `&12 * (x + &1) = &12 * x + &12`;
              REAL_ARITH `&12 * (x + &1) + &1 = &12 * x + &13`] THEN
  REAL_ARITH_TAC);;

let STIRLING_REMAINDER_MONO = prove
 (`!m n. 1 <= n /\ n <= m
         ==> stirling_remainder n - &1 / (&12 * &n) <=
             stirling_remainder m - &1 / (&12 * &m) /\
             stirling_remainder m - &1 / (&12 * &m + &1) <=
             stirling_remainder n - &1 / (&12 * &n + &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `n:num <= m` THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  SPEC_TAC(`p:num`, `p:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  MP_TAC(SPEC `n + p:num` STIRLING_REMAINDER_STEP_MONO) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let LOG_WALLIS_QUOTIENT = prove
 (`!m. 1 <= m
       ==> log(&16 pow m * &(FACT m) pow 4 /
               (&(FACT(2 * m)) * &(FACT(2 * m + 1)))) =
           &4 * stirling_remainder m - &2 * stirling_remainder(2 * m) +
           log(&2 * pi) + log(&m) - log(&2) - log(&2 * &m + &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stirling_remainder] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&0 < &m /\ &0 < &(FACT m) /\ &0 < &(FACT(2 * m))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 pow m = &2 pow (4 * m)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * &m + &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow (4 * m) /\
                &0 < &(FACT m) pow 4 /
                     (&(FACT (2 * m)) * (&2 * &m + &1) * &(FACT (2 * m)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL] THEN
  ASM_SIMP_TAC[LOG_DIV; LOG_MUL; LOG_POW; REAL_LT_MUL; REAL_POW_LT;
               REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

let STIRLING_REMAINDER_LIMIT = prove
 (`(stirling_remainder ---> &0) sequentially`,
  SUBGOAL_THEN `?l. (stirling_remainder ---> l) sequentially`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\n. stirling_remainder(n + 1) - &1 / (&12 * &(n + 1) + &1)`
                 CONVERGENT_REAL_BOUNDED_MONOTONE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `abs(stirling_remainder 1) + &1` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        X_GEN_TAC `n:num` THEN
        MP_TAC(SPECL [`n + 1`; `1`] STIRLING_REMAINDER_MONO) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&1 <= &(n + 1)` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
        SPEC_TAC(`&(n + 1)`, `x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `&0 <= inv(&12 * x + &1) /\ inv(&12 * x + &1) <= inv(&12 * x) /\
          inv(&12 * x) <= inv(&12)`
        MP_TAC THENL
         [REPEAT CONJ_TAC THENL
           [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN REAL_ARITH_TAC;
        DISJ2_TAC THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
        MP_TAC(SPECL [`SUC n + 1`; `n + 1`] STIRLING_REMAINDER_MONO) THEN
        ANTS_TAC THENL [ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN EXISTS_TAC `l:real` THEN
    MATCH_MP_TAC REAL_SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_STRADDLE THEN
    EXISTS_TAC
     `\n. stirling_remainder(n + 1) - &1 / (&12 * &(n + 1) + &1)` THEN
    EXISTS_TAC
     `\n. (stirling_remainder(n + 1) - &1 / (&12 * &(n + 1) + &1)) +
          inv(&n + &1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[REAL_ARITH `(a:real) <= a - b + c <=> b <= c`;
                  GSYM REAL_OF_NUM_ADD; real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
      MATCH_MP_TAC REALLIM_ADD THEN
      ASM_REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `l = &0` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `&4 * l - &2 * l = &0 ==> l = &0`) THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\m. &4 * stirling_remainder m - &2 * stirling_remainder(2 * m)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_LMUL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[TENDSTO_REAL] THEN
    SUBGOAL_THEN `lift o (\m. stirling_remainder(2 * m)) =
                  (lift o stirling_remainder) o (\m. 2 * m)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM];
      MATCH_MP_TAC LIM_SUBSEQUENCE THEN
      ASM_REWRITE_TAC[GSYM TENDSTO_REAL] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\m. log((&2 pow m * &(FACT m)) pow 4 /
            (&(FACT(2 * m)) * &(FACT(2 * m + 1)))) +
        log(&2 + inv(&m)) - log(&2 * pi) + log(&2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(&2 pow m * &(FACT m)) pow 4 / (&(FACT(2 * m)) * &(FACT(2 * m + 1))) =
      &16 pow m * &(FACT m) pow 4 / (&(FACT(2 * m)) * &(FACT(2 * m + 1)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_POW_MUL; REAL_POW_POW; REAL_MUL_ASSOC] THEN
      REPEAT AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_WALLIS_QUOTIENT] THEN
    SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 + inv(&m) = (&2 * &m + &1) / &m` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < x ==> &0 < &2 * x + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = log(pi / &2) + log(&2 + &0) - log(&2 * pi) + log(&2)`
  SUBST1_TAC THENL
   [MP_TAC PI_POS THEN DISCH_TAC THEN
    ASM_SIMP_TAC[LOG_DIV; LOG_MUL; REAL_ADD_RID; REAL_ARITH `&0 < &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN REWRITE_TAC[WALLIS] THEN
    SIMP_TAC[REAL_CONTINUOUS_AT_LOG; PI_POS; REAL_LT_DIV;
             REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  REPEAT(FIRST[MATCH_ACCEPT_TAC REALLIM_CONST;
               MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC;
               MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC]) THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
  SIMP_TAC[REAL_CONTINUOUS_AT_LOG; REAL_ARITH `&0 < &2 + &0`] THEN
  MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST; REALLIM_1_OVER_N]);;

let STIRLING_REMAINDER_BOUNDS = prove
 (`!n. 1 <= n
       ==> &1 / (&12 * &n + &1) <= stirling_remainder n /\
           stirling_remainder n <= &1 / (&12 * &n)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!c. &0 <= c
        ==> ((\m. stirling_remainder m - &1 / (&12 * &m + c)) ---> &0)
            sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[STIRLING_REMAINDER_LIMIT] THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN EXISTS_TAC `\m. inv(&m)` THEN
    REWRITE_TAC[REALLIM_1_OVER_N; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= &m` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `(e:real) <= x <=> &0 <= x - e`] THEN
    MATCH_MP_TAC(ISPECL [`sequentially`;
                         `\m. stirling_remainder m - &1 / (&12 * &m + &1)`]
                        REALLIM_UBOUND) THEN
    ASM_SIMP_TAC[REAL_POS; TRIVIAL_LIMIT_SEQUENTIALLY;
                 EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN ASM_SIMP_TAC[STIRLING_REMAINDER_MONO];
    ONCE_REWRITE_TAC[REAL_ARITH `x <= (e:real) <=> x - e <= &0`] THEN
    MATCH_MP_TAC(ISPECL [`sequentially`;
                         `\m. stirling_remainder m - &1 / (&12 * &m + &0)`]
                        REALLIM_LBOUND) THEN
    ASM_SIMP_TAC[REAL_POS; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY;
                 REAL_LE_REFL] THEN
    EXISTS_TAC `n:num` THEN
    ASM_SIMP_TAC[REAL_ADD_RID; STIRLING_REMAINDER_MONO]]);;

let STIRLING_FACT_BOUNDS = prove
 (`!n. 1 <= n
       ==> sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
           exp(&1 / (&12 * &n + &1)) <= &(FACT n) /\
           &(FACT n) <=
           sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp(&1 / (&12 * &n))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `n:num` STIRLING_REMAINDER_BOUNDS) THEN
  ASM_REWRITE_TAC[stirling_remainder] THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &(FACT n) /\ &0 < pi` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; PI_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp e /\
        log(sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp e) =
        log(&2 * pi) / &2 + (&n + &1 / &2) * log(&n) - &n + e`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&0 < &2 * pi * &n` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(&2 * pi * &n) /\ &0 < (&n / exp(&1)) pow n`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_EXP_POS_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT; LOG_MUL; LOG_SQRT; LOG_POW;
                 LOG_DIV; LOG_EXP; REAL_LT_DIV] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
                    exp(&1 / (&12 * &n + &1))`; `&(FACT n)`] LOG_MONO_LE);
    MP_TAC(ISPECL [`&(FACT n)`; `sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
                    exp(&1 / (&12 * &n))`] LOG_MONO_LE)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let STIRLING_FACT_LIMIT = prove
 (`((\n. &(FACT n) / (sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n)) ---> &1)
   sequentially`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. exp(stirling_remainder n)` THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_EXP_0] THEN
    MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_EXP; STIRLING_REMAINDER_LIMIT]] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &(FACT n) /\ &0 < pi` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; PI_POS] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * pi * &n` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n` ASSUME_TAC
  THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `exp(log(&(FACT n) / (sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n)))` THEN
  CONJ_TAC THENL [AP_TERM_TAC; ASM_SIMP_TAC[EXP_LOG; REAL_LT_DIV]] THEN
  ASM_SIMP_TAC[stirling_remainder; LOG_DIV; LOG_MUL; LOG_SQRT; LOG_POW;
               LOG_EXP; SQRT_POS_LT; REAL_POW_LT; REAL_LT_DIV;
               REAL_EXP_POS_LT; REAL_ARITH `&0 < &2`] THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  REAL_ARITH_TAC);;

let STIRLING_OUTER_BOUNDS = prove
 (`!n. 2 <= n
       ==> exp(&1) * (&n / exp(&1)) pow n
             <= sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
                exp(&1 / (&12 * &n + &1)) /\
           sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp(&1 / (&12 * &n))
             <= exp(&1) * &n * (&n / exp(&1)) pow n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 <= &n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&n / exp(&1)) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MP_TAC PI_BOUNDS_3927 THEN MP_TAC EXP_1_BOUNDS THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `(x:real) * p <= (s * e) * p ==> x * p <= s * p * e`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `sqrt(&2 * pi * &n)` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&3` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN
      TRANS_TAC REAL_LE_TRANS `&4 * pi` THEN CONJ_TAC THENL
       [CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_ARITH `&2 * p * n = (&2 * n) * p`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC(SPEC `&1 / (&12 * &n + &1)` REAL_EXP_LE_X) THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 + x <= y ==> &1 <= y`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `((s:real) * e) * p <= (x * n) * p ==> s * p * e <= x * n * p`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(&1 / (&12 * &n)) = sqrt(exp(&1 / (&6 * &n)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC[REAL_EXP_POS_LE; GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&2 <= &n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  MP_TAC(SPEC `&23 / &24` REAL_EXP_LE_X) THEN
  SUBGOAL_THEN `exp(&1) pow 2 = exp(&1 / &12) * exp(&23 / &24) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&1 / (&6 * &n)) <= exp(&1 / &12)` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&1 / (&6 * &n)` REAL_EXP_POS_LT) THEN
  MP_TAC(SPEC `&1 / &12` REAL_EXP_POS_LT) THEN
  UNDISCH_TAC `&2 <= &n` THEN MP_TAC PI_POS THEN
  UNDISCH_TAC `pi < &3927 / &1250` THEN
  SPEC_TAC(`exp(&1 / (&6 * &n))`, `a:real`) THEN
  SPEC_TAC(`exp(&1 / &12)`, `b:real`) THEN
  SPEC_TAC(`exp(&23 / &24)`, `c:real`) THEN
  SPEC_TAC(`&n`, `x:real`) THEN SPEC_TAC(`pi`, `p:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real) <= c pow 2` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&1 + &23 / &24) pow 2` THEN CONJ_TAC THENL
     [CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&2 * p * x) * b` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `((x:real) * x) * (p * b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(&2 * x) * (p * b) <= (x * x) * (p * b)
                             ==> (&2 * p * x) * b <= (x * x) * (p * b)`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH
     `((x * x) * b) * p <= ((x * x) * b) * c
      ==> ((x:real) * x) * (p * b) <= (b * c) * x pow 2`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_SQUARE; REAL_LT_IMP_LE]]);;

let STIRLING_INEQUALITY = prove
 (`!n. 2 <= n
       ==> exp(&1) * (&n / exp(&1)) pow n
             <= sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
                exp(&1 / (&12 * &n + &1)) /\
           sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
           exp(&1 / (&12 * &n + &1)) <= &(FACT n) /\
           &(FACT n) <=
           sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp(&1 / (&12 * &n)) /\
           sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp(&1 / (&12 * &n))
             <= exp(&1) * &n * (&n / exp(&1)) pow n`,
  SIMP_TAC[STIRLING_OUTER_BOUNDS; STIRLING_FACT_BOUNDS;
           ARITH_RULE `2 <= n ==> 1 <= n`]);;

let FACT_EXP_BOUNDS = prove
 (`!n. 1 <= n
       ==> exp(&1) * (&n / exp(&1)) pow n <= &(FACT n) /\
           &(FACT n) <= exp(&1) * &n * (&n / exp(&1)) pow n`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[FACT_LE_EXP_MUL_POW] THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(SPEC `&1` REAL_EXP_POS_LT) THEN CONV_TAC REAL_FIELD;
    MP_TAC(SPEC `n:num` STIRLING_INEQUALITY) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

let STIRLING_INEQUALITY_COUNTEREXAMPLE = prove
 (`~(!n. 1 <= n
         ==> exp(&1) * (&n / exp(&1)) pow n
               <= sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n *
                  exp(&1 / (&12 * &n + &1))) /\
   ~(!n. 1 <= n
         ==> sqrt(&2 * pi * &n) * (&n / exp(&1)) pow n * exp(&1 / (&12 * &n))
               <= exp(&1) * &n * (&n / exp(&1)) pow n)`,
  CONJ_TAC THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_1; REAL_MUL_RID; REAL_MUL_LID] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[REAL_ARITH `(s:real) * &1 / e * x = (s * x) / e`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LID;
               REAL_EXP_POS_LT] THEN
  SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_RINV; REAL_EXP_NZ] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_EXP_POS_LE; REAL_POS; PI_POS_LE;
           REAL_POW_MUL; SQRT_POW_2] THENL
   [SUBGOAL_THEN `exp(&1) pow 2 = exp(&2)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `&1 / &26` REAL_EXP_DOUBLE_LE) THEN
    MP_TAC(SPECL [`7`; `&2`] REAL_EXP_PARTIAL_SUM_LE) THEN
    REWRITE_TAC[TOP_DEPTH_CONV num_CONV `7`; SUM_CLAUSES_NUMSEG; LE_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[FACT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `exp(&1 / &13) pow 2 <= (&27 / &25) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN
    TRANS_TAC REAL_LET_TRANS `(&2 * pi) * &729 / &625` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MP_TAC PI_BOUNDS_3927 THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `exp(&1) pow 2 = exp(&1 / &8) pow 16 /\
                  exp(inv(&12)) pow 2 = exp(&1 / &6)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM REAL_EXP_N] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(&1 / &8) pow 16 <= (&17 / &15) pow 16` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MP_TAC(SPEC `&1 / &16` REAL_EXP_DOUBLE_LE) THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`3`; `&1 / &6`] REAL_EXP_PARTIAL_SUM_LE) THEN
    REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`; SUM_CLAUSES_NUMSEG; LE_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[FACT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    TRANS_TAC REAL_LET_TRANS
     `&48661191875666868481 / &6568408355712890625` THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LTE_TRANS `(&2 * pi) * &1531 / &1296` THEN CONJ_TAC THENL
     [MP_TAC PI_BOUNDS_3927 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The central binomial coefficient: 4^n/sqrt(pi n) (1 - 1/(8n)) <= C(2n,n)  *)
(* <= 4^n/sqrt(pi n) (1 - 1/(9n)), from the Robbins bounds.                  *)
(* ------------------------------------------------------------------------- *)

let LOG_CENTRAL_BINOM = prove
 (`!n. 1 <= n
       ==> log(&(binom(2 * n,n))) =
           log(&4 pow n / sqrt(pi * &n)) +
           (stirling_remainder(2 * n) - &2 * stirling_remainder n)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[stirling_remainder] THEN
  MP_TAC(SPECL [`n:num`; `n:num`] BINOM_FACT) THEN
  REWRITE_TAC[GSYM MULT_2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN
   `&0 < &n /\ &0 < &(FACT n) /\ &0 < &(binom(2 * n,n)) /\ &0 < pi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; PI_POS; LT_NZ; BINOM_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 pow n = &2 pow n * &2 pow n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_DIV; LOG_SQRT; LOG_POW; REAL_LT_MUL; REAL_POW_LT;
               SQRT_POS_LT; REAL_ARITH `&0 < &2`] THEN
  REAL_ARITH_TAC);;

let CENTRAL_BINOM_LOWER_MARGIN = prove
 (`!z. &1 <= z
       ==> &1 - &1 / (&8 * z) <=
           &1 - (&1 / (&6 * z) - &1 / (&24 * z + &1)) +
           (&1 / (&6 * z) - &1 / (&24 * z + &1)) pow 2 / &2 -
           (&1 / (&6 * z) - &1 / (&24 * z + &1)) pow 3 / &6`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC
   `(&108864 * z pow 4 + &12960 * z pow 3 + &54 * z pow 2 - &36 * z - &1) /
    (&1296 * z pow 3 * (&24 * z + &1) pow 3)`
   (REAL_ARITH `!c a b:real. a - b = c /\ &0 <= c ==> b <= a`)) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&1 <= z` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [SUBGOAL_THEN `z <= z pow 4 /\ &0 <= z pow 3 /\ &0 <= z pow 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= z ==> &0 <= z`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC]);;

let CENTRAL_BINOM_UPPER_MARGIN = prove
 (`!z. &2 <= z
       ==> &1 - (&2 / (&12 * z + &1) - &1 / (&24 * z)) +
           (&2 / (&12 * z + &1) - &1 / (&24 * z)) pow 2 / &2
           <= &1 - &1 / (&9 * z)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC
   `(&2304 * z pow 3 - &3216 * z pow 2 - &104 * z - &1) /
    (&1152 * z pow 2 * (&12 * z + &1) pow 2)`
   (REAL_ARITH `!c a b:real. a - b = c /\ &0 <= c ==> b <= a`)) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&2 <= z` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 * z pow 2 <= z * z pow 2 /\ &2 * z <= z * z`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&2 <= z ==> &0 <= z`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow); GSYM REAL_POW_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC]);;

let CENTRAL_BINOM_INEQUALITY = prove
 (`!n. 1 <= n
       ==> &4 pow n / sqrt(pi * &n) * (&1 - &1 / (&8 * &n))
             <= &(binom(2 * n,n)) /\
           &(binom(2 * n,n))
             <= &4 pow n / sqrt(pi * &n) * (&1 - &1 / (&9 * &n))`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[BINOM_1; REAL_MUL_RID; REAL_POW_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BINOM_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MP_TAC PI_BOUNDS_3927 THEN STRIP_TAC THEN
    SUBGOAL_THEN `&7 / &4 <= sqrt pi /\ sqrt pi <= &16 / &9`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT; MATCH_MP_TAC REAL_LE_LSQRT] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt pi` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(a:real) / s * b = (a * b) / s`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `n:num` LOG_CENTRAL_BINOM) THEN
  MP_TAC(SPEC `n:num` STIRLING_REMAINDER_BOUNDS) THEN
  MP_TAC(SPEC `2 * n` STIRLING_REMAINDER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_LID] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `inv(&24 * &n + &1) - inv(&6) * inv(&n)
      <= log(&(binom(2 * n,n))) - log(&4 pow n * inv(sqrt(pi * &n))) /\
    log(&(binom(2 * n,n))) - log(&4 pow n * inv(sqrt(pi * &n)))
      <= inv(&24) * inv(&n) - &2 * inv(&12 * &n + &1)`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_ARITH `inv(x:real) = &1 / x`] THEN
  POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < &(binom(2 * n,n)) /\ &0 < &4 pow n / sqrt(pi * &n)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; BINOM_EQ_0] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &4`] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[PI_POS; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(binom(2 * n,n)) =
    &4 pow n / sqrt(pi * &n) *
    exp(log(&(binom(2 * n,n))) - log(&4 pow n / sqrt(pi * &n)))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SPEC_TAC(`log(&(binom(2 * n,n))) - log(&4 pow n / sqrt(pi * &n))`,
           `t:real`) THEN
  GEN_TAC THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP;
               REAL_ARITH `(a + t) - a:real = t`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &4 pow n / sqrt(pi * &n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPEC `&n` CENTRAL_BINOM_LOWER_MARGIN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(--(&1 / (&6 * &n) - &1 / (&24 * &n + &1)))` THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `&1 / (&6 * &n) - &1 / (&24 * &n + &1)`
        (GEN `x:real` (EXPAND_PARTIAL_SUM_RULE
           (SPECL [`1`; `--x:real`] REAL_EXP_PARTIAL_SUM_ODD_LE)))) THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `&n` CENTRAL_BINOM_UPPER_MARGIN) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= c ==> a <= c`) THEN
    TRANS_TAC REAL_LE_TRANS
     `exp(--(&2 / (&12 * &n + &1) - &1 / (&24 * &n)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&2 / (&12 * &n + &1) - &1 / (&24 * &n)`
        (GEN `x:real` (EXPAND_PARTIAL_SUM_RULE
           (SPECL [`1`; `--x:real`] REAL_EXP_LE_PARTIAL_SUM_EVEN)))) THEN
      ANTS_TAC THENL [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`);
                      REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `inv(&24 * &n) <= inv(&12 * &n + &1) /\
                    &0 <= inv(&12 * &n + &1)` MP_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[real_div; REAL_MUL_LID] THEN REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The binary entropy H in bits, and the entropy bounds (sqrt pi/2) G <=     *)
(* C(n,k) <= G, G = 2^(n H(a))/sqrt(2 pi n a (1-a)).                         *)
(* ------------------------------------------------------------------------- *)

let binary_entropy = new_definition
 `binary_entropy x = --(x * log x + (&1 - x) * log(&1 - x)) / log(&2)`;;

let BINARY_ENTROPY_0_1 = prove
 (`binary_entropy(&0) = &0 /\ binary_entropy(&1) = &0`,
  REWRITE_TAC[binary_entropy; REAL_SUB_REFL; REAL_SUB_RZERO; LOG_1] THEN
  REAL_ARITH_TAC);;

let BINARY_ENTROPY_RATIO_LOG = prove
 (`!n k a. k <= n /\ &k = a * &n
           ==> &n * binary_entropy a * log(&2) =
               &n * log(&n) - &k * log(&k) - &(n - k) * log(&(n - k))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `0 < k /\ k < n` THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC;
    ASM_CASES_TAC `n = 0` THENL
     [SUBGOAL_THEN `k = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `n = 0` THEN DISCH_THEN SUBST_ALL_TAC THEN
      REWRITE_TAC[SUB_0; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `k = 0 \/ k = n` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `a = &0` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 = a * &n` THEN UNDISCH_TAC `&0 < &n` THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[BINARY_ENTROPY_0_1; SUB_0] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `a = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `&n = a * &n` THEN UNDISCH_TAC `&0 < &n` THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[BINARY_ENTROPY_0_1; SUB_REFL] THEN REAL_ARITH_TAC]]] THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &k /\ &0 < &(n - k) /\ &0 < log(&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log a = log(&k) - log(&n) /\
                log(&1 - a) = log(&(n - k)) - log(&n)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - a = &(n - k) / &n /\ a = &k / &n`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE; REAL_EQ_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN MATCH_MP_TAC LOG_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[binary_entropy] THEN
  SUBGOAL_THEN `~(log(&2) = &0)`
   (fun th -> REWRITE_TAC[MATCH_MP REAL_DIV_RMUL th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(n - k) = &n - &k` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&k = a * &n` THEN
  SPEC_TAC(`log(&k)`, `p:real`) THEN
  SPEC_TAC(`log(&n)`, `q:real`) THEN SPEC_TAC(`log(&n - &k)`, `r:real`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let LOG_BINOM_ENTROPY = prove
 (`!n k a.
     0 < k /\ k < n /\ &k = a * &n
     ==> log(&(binom(n,k))) =
         log(&2 rpow (&n * binary_entropy a) /
             sqrt(&2 * pi * &n * a * (&1 - a))) +
         (stirling_remainder n - stirling_remainder k -
          stirling_remainder(n - k))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[stirling_remainder] THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `a:real`] BINARY_ENTROPY_RATIO_LOG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LT_IMP_LE]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &k /\ &0 < &(n - k) /\ &0 < pi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; PI_POS] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * pi * &n * a * (&1 - a) =
                &2 * pi * &k * &(n - k) / &n`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < &n` THEN UNDISCH_TAC `&k = a * &n` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `&k = a * &n` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < &(FACT k) /\ &0 < &(FACT(n - k)) /\
                &0 < &(binom(n,k))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; LT_NZ; BINOM_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * pi * &k * &(n - k) / &n` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&2 rpow (&n * binary_entropy a) /
        sqrt(&2 * pi * &k * &(n - k) / &n)) =
    &n * binary_entropy a * log(&2) -
    log(&2 * pi * &k * &(n - k) / &n) / &2`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_DIV; RPOW_POS_LT; SQRT_POS_LT; LOG_RPOW; LOG_SQRT;
                 REAL_ARITH `&0 < &2`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    UNDISCH_TAC `&n * binary_entropy a * log (&2) =
                 &n * log (&n) - &k * log (&k) -
                 &(n - k) * log (&(n - k))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi * &k * &(n - k) / &n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * pi * &k * &(n - k) / &n) =
                log(&2) + log pi + log(&k) + log(&(n - k)) - log(&n)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_DIV; REAL_LT_MUL; REAL_LT_DIV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n - k:num`; `k:num`] BINOM_FACT) THEN
  SUBGOAL_THEN `(n - k) + k = (n:num)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
  DISCH_THEN(MP_TAC o AP_TERM `log`) THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  SUBGOAL_THEN `&(n - k) = &n - &k` MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SQRT_PI_HALF_LE_EXP = prove
 (`sqrt pi / &2 <= exp(--(&29 / &296))`,
  MATCH_MP_TAC(REAL_ARITH `s <= &2 * e ==> s / &2 <= e`) THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SIMP_TAC[REAL_LE_MUL; REAL_EXP_POS_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM REAL_EXP_N; REAL_EXP_NEG] THEN
  MP_TAC(SPEC `&29 / &296` REAL_EXP_DOUBLE_LE) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ARITH `-- &29 / &148 = --(&29 / &148)`; REAL_EXP_NEG] THEN
  MP_TAC(SPEC `&29 / &148` REAL_EXP_POS_LT) THEN
  MP_TAC PI_BOUNDS_3927 THEN MP_TAC PI_POS THEN
  SPEC_TAC(`exp(&29 / &148)`, `e:real`) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `pi * &325 / &267` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let RECIP_DIFF_13_LE = prove
 (`!z. &2 <= z ==> &1 / (&12 * z) - &1 / (&12 * z + &13) <= &13 / &888`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC
   `&13 * (&144 * z pow 2 + &156 * z - &888) /
    (&888 * &12 * z * (&12 * z + &13))`
   (REAL_ARITH `!c a b:real. a - b = c /\ &0 <= c ==> b <= a`)) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `&2 <= z` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 * z <= z pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC]);;

let STIRLING_REMAINDER_BINOM_BOUND = prove
 (`!k m. 1 <= k /\ 1 <= m /\ ~(k = 1 /\ m = 1)
         ==> &1 / (&12 * &k) + &1 / (&12 * &m) - &1 / (&12 * &(k + m) + &1)
             <= &29 / &296`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&0 <= &1 / (&12 * (&k + &m) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [UNDISCH_TAC `k = 1` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `&m` RECIP_DIFF_13_LE) THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&12 * (&1 + m) + &1 = &12 * m + &13`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [UNDISCH_TAC `m = 1` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `&k` RECIP_DIFF_13_LE) THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&12 * (k + &1) + &1 = &12 * k + &13`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / (&12 * &k) <= &1 / &24 /\ &1 / (&12 * &m) <= &1 / &24`
  MP_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let BINARY_ENTROPY_HALF = prove
 (`binary_entropy(&1 / &2) = &1`,
  REWRITE_TAC[binary_entropy] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2`; LOG_1] THEN
  SUBGOAL_THEN `&0 < log(&2)` MP_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let BINOM_ENTROPY_INEQUALITY = prove
 (`!n k a. 0 < k /\ k < n /\ &k = a * &n
           ==> sqrt pi / &2 *
               (&2 rpow (&n * binary_entropy a) /
                sqrt(&2 * pi * &n * a * (&1 - a))) <= &(binom(n,k)) /\
               &(binom(n,k)) <=
               &2 rpow (&n * binary_entropy a) /
               sqrt(&2 * pi * &n * a * (&1 - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n /\ &0 < &k /\ &k < &n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a /\ a < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real) = &k / &n` SUBST1_TAC THENL
     [SIMP_TAC[REAL_EQ_RDIV_EQ; ASSUME `&0 < &n`; ASSUME `&k = a * &n`];
      ALL_TAC] THEN
    SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID; ASSUME `&0 < &n`;
             ASSUME `&0 < &k`; ASSUME `&k < &n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 rpow (&n * binary_entropy a) /
                    sqrt(&2 * pi * &n * a * (&1 - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `a:real`] LOG_BINOM_ENTROPY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPEC `n:num` STIRLING_REMAINDER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `k:num` STIRLING_REMAINDER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `n - k:num` STIRLING_REMAINDER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 / (&12 * &n) <= &1 / (&12 * &k + &1) /\
                &0 <= &1 / (&12 * &(n - k) + &1)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT;
                  REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&(binom(n,k))) -
    log(&2 rpow (&n * binary_entropy a) / sqrt(&2 * pi * &n * a * (&1 - a)))
    <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(binom(n,k))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; BINOM_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G = &2 rpow (&n * binary_entropy a) /
                  sqrt(&2 * pi * &n * a * (&1 - a))` THEN
  SUBGOAL_THEN `&(binom(n,k)) = G * exp(log(&(binom(n,k))) - log G)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [SIMP_TAC[REAL_EXP_SUB; EXP_LOG; ASSUME `&0 < G`;
             ASSUME `&0 < &(binom(n,k))`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; ASSUME `&0 < G`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(s:real) * g <= e * g ==> s * g <= g * e`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
  ASM_CASES_TAC `k = 1 /\ n = 2` THENL
   [ALL_TAC;
    TRANS_TAC REAL_LE_TRANS `exp(--(&29 / &296))` THEN
    REWRITE_TAC[SQRT_PI_HALF_LE_EXP; REAL_EXP_MONO_LE] THEN
    MP_TAC(SPECL [`k:num`; `n - k:num`] STIRLING_REMAINDER_BINOM_BOUND) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k + (n - k) = (n:num)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC] THEN
  UNDISCH_TAC `k = 1 /\ n = 2` THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `a = &1 / &2` SUBST_ALL_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&2 rpow (&2 * binary_entropy (&1 / &2)) /
               sqrt(&2 * pi * &2 * &1 / &2 * (&1 - &1 / &2)) = G` THEN
  REWRITE_TAC[BINARY_ENTROPY_HALF; REAL_MUL_RID; RPOW_POW;
              REAL_ARITH `&2 * pi * &2 * &1 / &2 * (&1 - &1 / &2) = pi`] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[BINOM_1] THEN
  SUBGOAL_THEN `&0 < sqrt pi` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EXP_SUB; EXP_LOG; REAL_LT_DIV;
               REAL_ARITH `&0 < &2 /\ &0 < &4`] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  UNDISCH_TAC `&0 < sqrt pi` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Basic facts on H, and H(x) <= x lg(4/x) and H(x) <= (1-x) lg(4/(1-x)).    *)
(* ------------------------------------------------------------------------- *)

let BINARY_ENTROPY_SYM = prove
 (`!x. binary_entropy(&1 - x) = binary_entropy x`,
  REWRITE_TAC[binary_entropy; REAL_ARITH `&1 - (&1 - x) = x`] THEN
  REAL_ARITH_TAC);;

let BINARY_ENTROPY_LE_MUL_LOG = prove
 (`!x. &0 <= x /\ x <= &1 ==> binary_entropy x <= x * log(&4 / x) / log(&2)`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_MUL_LZERO; real_div;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &1` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_MUL_LID; REAL_DIV_1] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_LT_IMP_LE; LOG_2_POS] THEN
    MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[binary_entropy] THEN
  REWRITE_TAC[REAL_ARITH `(x:real) * l / m = (x * l) / m`] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; LOG_2_POS] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &4`] THEN
  MP_TAC(SPEC `--(x:real)` LOG_RATIONAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_sub] THEN STRIP_TAC THEN
  SUBGOAL_THEN `log(&4) = &2 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `--((&1 - x) * log(&1 - x)) <= x` MP_TAC THENL
   [UNDISCH_TAC `--x / (&1 - x) <= log (&1 - x)` THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; ASSUME `x < &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x * &56 / &81 <= x * log(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[LOG_2_RATIONAL_BOUNDS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_LE_MUL_LOG_ALT = prove
 (`!x. &0 <= x /\ x <= &1
       ==> binary_entropy x <= (&1 - x) * log(&4 / (&1 - x)) / log(&2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM BINARY_ENTROPY_SYM] THEN
  MATCH_MP_TAC BINARY_ENTROPY_LE_MUL_LOG THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Quadratic bounds on H: 1 - 4x^2 <= H(1/2 - x) <= 1 - (2/ln 2) x^2, and    *)
(* 4x(1-x) <= H(x).                                                          *)
(* ------------------------------------------------------------------------- *)

let BINARY_ENTROPY_HALF_SUB_UPPER = prove
 (`!x. &0 <= x /\ x < &1 / &2
       ==> binary_entropy(&1 / &2 - x) <= &1 - &2 / log(&2) * x pow 2`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[binary_entropy;
              REAL_ARITH `&1 - (&1 / &2 - x) = &1 / &2 + x`] THEN
  SUBGOAL_THEN
   `&0 <= log(&2) - &2 * x pow 2 + (&1 / &2 - x) * log(&1 / &2 - x) +
         (&1 / &2 + x) * log(&1 / &2 + x)`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\x. log(&2) - &2 * x pow 2 + (&1 / &2 - x) * log(&1 / &2 - x) +
           (&1 / &2 + x) * log(&1 / &2 + x)`;
      `\x. log(&1 / &2 + x) - log(&1 / &2 - x) - &4 * x`;
      `{x:real | &0 <= x /\ x < &1 / &2}`; `&0`; `x:real`]
     HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2`; LOG_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_ARITH `log(&2) - &0 + &1 / &2 * (&0 - log(&2)) +
                             &1 / &2 * (&0 - log(&2)) = &0`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      SUBGOAL_THEN `(&1 / &2 - y) * inv(&1 / &2 - y) = &1 /\
                    (&1 / &2 + y) * inv(&1 / &2 + y) = &1` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MP_TAC(SPEC `&2 * y` LOG_RATIO_ODD_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `(&1 + &2 * y) / (&1 - &2 * y) = (&1 / &2 + y) / (&1 / &2 - y)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ a * d = c * b
                                 ==> a / b = c / d`) THEN
        REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[LOG_DIV; ASSUME `y < &1 / &2`; REAL_SUB_LT;
               REAL_ARITH `&0 <= y ==> &0 < &1 / &2 + y`;
               ASSUME `&0 <= y`] THEN
      SUBGOAL_THEN `&0 <= &2 * (&2 * y) pow 3 / &3` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `&1 - &2 / log(&2) * x pow 2 = (log(&2) - &2 * x pow 2) / log(&2)`
  SUBST1_TAC THENL
   [MP_TAC LOG_2_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; LOG_2_POS] THEN ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_HALF_SUB_LOWER = prove
 (`!u. &0 <= u /\ u <= &3 / &10
       ==> &1 - &4 * u pow 2 <= binary_entropy(&1 / &2 - u)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[binary_entropy;
              REAL_ARITH `&1 - (&1 / &2 - x) = &1 / &2 + x`] THEN
  SUBGOAL_THEN
   `&0 <= --((&1 / &2 - u) * log(&1 / &2 - u) +
             (&1 / &2 + u) * log(&1 / &2 + u)) -
          log(&2) + &4 * log(&2) * u pow 2`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\u. --((&1 / &2 - u) * log(&1 / &2 - u) +
              (&1 / &2 + u) * log(&1 / &2 + u)) -
           log(&2) + &4 * log(&2) * u pow 2`;
      `\u. log(&1 / &2 - u) - log(&1 / &2 + u) + &8 * log(&2) * u`;
      `{x:real | &0 <= x /\ x <= &3 / &10}`; `&0`; `u:real`]
     HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM; IS_REALINTERVAL_CLAUSES; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2`; LOG_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_ARITH `--(&1 / &2 * (&0 - l) + &1 / &2 * (&0 - l)) - l +
                             &4 * l * &0 = &0`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      SUBGOAL_THEN `(&1 / &2 - y) * inv(&1 / &2 - y) = &1 /\
                    (&1 / &2 + y) * inv(&1 / &2 + y) = &1` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPEC `&2 * y` LOG_RATIO_ODD_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 + &2 * y) / (&1 - &2 * y) = (&1 / &2 + y) / (&1 / &2 - y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD `~(b = &0) /\ ~(d = &0) /\ a * d = c * b
                               ==> a / b = c / d`) THEN
      REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `y <= &3 / &10 ==> &0 < &1 / &2 - y`;
             REAL_ARITH `&0 <= y ==> &0 < &1 / &2 + y`; ASSUME `&0 <= y`;
             ASSUME `y <= &3 / &10`] THEN
    SUBGOAL_THEN `&0 < &3 * (&1 - (&2 * y) pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_ARITH `&0 < &3`] THEN
      REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 * y) pow 3 / (&3 * (&1 - (&2 * y) pow 2)) <= &3 / &8 * y`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `y * y pow 2 <= y * &9 / &100` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC REAL_LE_TRANS `(&3 / &10) pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
          CONV_TAC REAL_RAT_REDUCE_CONV];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&56 / &81 * y <= log(&2) * y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[LOG_2_RATIONAL_BOUNDS];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN SIMP_TAC[REAL_LE_RDIV_EQ; LOG_2_POS] THEN
  ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_GE_QUADRATIC_SMALL = prove
 (`!x. &0 < x /\ x <= &1 / &5 ==> &4 * x * (&1 - x) <= binary_entropy x`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[binary_entropy] THEN SIMP_TAC[REAL_LE_RDIV_EQ; LOG_2_POS] THEN
  SUBGOAL_THEN `x * (&1 - x) <= --((&1 - x) * log(&1 - x))` ASSUME_TAC THENL
   [MP_TAC(SPEC `--(x:real)` LOG_RATIONAL_BOUNDS) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_sub] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `(&1 - x) * l <= (&1 - x) * --x
                             ==> x * (&1 - x) <= --((&1 - x) * l)`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = (&1 - x) / (&1 + x)` THEN
  SUBGOAL_THEN `&2 / &3 <= t /\ t < &1 /\ (&1 + t) / (&1 - t) = inv x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
             REAL_ARITH `&0 < x ==> &0 < &1 + x`; ASSUME `&0 < x`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(SPEC `t:real` LOG_RATIO_ODD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_INV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&16 / &9 * (&1 - x) <= &2 * t + &2 * t pow 3 / &3`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `t * (&1 + x) = &1 - x` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 / &3) pow 2 <= t pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * (&2 + &2 * t pow 2 / &3 - &16 / &9 * (&1 + x))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `t * (&1 + x) = &1 - x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x * (&16 / &9 * (&1 - x)) <= x * --log x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x * (&1 - x)) * log(&2) <= (x * (&1 - x)) * &25 / &36`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[LOG_2_RATIONAL_BOUNDS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_GE_QUADRATIC = prove
 (`!x. &0 <= x /\ x <= &1 ==> &4 * x * (&1 - x) <= binary_entropy x`,
  SUBGOAL_THEN `!x. &0 <= x /\ x <= &1 / &2
                    ==> &4 * x * (&1 - x) <= binary_entropy x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `x <= &1 / &5` THENL
     [MATCH_MP_TAC BINARY_ENTROPY_GE_QUADRATIC_SMALL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `&1 / &2 - x` BINARY_ENTROPY_HALF_SUB_LOWER) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&1 / &2 - (&1 / &2 - x) = x`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= &1 / &2` THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM BINARY_ENTROPY_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - x`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let BINARY_ENTROPY_QUADRATIC_INEQUALITY_GEN = prove
 (`!x. abs x <= &1 / &2
       ==> &1 - &4 * x pow 2 <= binary_entropy(&1 / &2 - x) /\
           binary_entropy(&1 / &2 - x) <= &1 - &2 / log(&2) * x pow 2`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPEC `&1 / &2 - x` BINARY_ENTROPY_GE_QUADRATIC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. &0 <= y /\ y <= &1 / &2
                    ==> binary_entropy(&1 / &2 - y) <=
                        &1 - &2 / log(&2) * y pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `y = &1 / &2` THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; BINARY_ENTROPY_0_1] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      MP_TAC LOG_2_RATIONAL_BOUNDS THEN MP_TAC LOG_2_POS THEN
      SPEC_TAC(`log(&2)`, `l:real`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `&0 <= &1 - &2 / l * &1 / &4 <=>
                              &2 / l * &1 / &4 <= &1`] THEN
      REWRITE_TAC[REAL_ARITH `&2 / l * &1 / &4 = (&1 / &2) / l`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC BINARY_ENTROPY_HALF_SUB_UPPER THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= x` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM BINARY_ENTROPY_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 / &2 - x) = &1 / &2 - --x`] THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH_RULE `EVEN 2`]);;

let BINARY_ENTROPY_QUADRATIC_INEQUALITY = prove
 (`!x. abs x <= &1 / &2
       ==> &1 - &5 * x pow 2 <= binary_entropy(&1 / &2 - x) /\
           binary_entropy(&1 / &2 - x) <= &1 - x pow 2`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    BINARY_ENTROPY_QUADRATIC_INEQUALITY_GEN) THEN
  SUBGOAL_THEN `x pow 2 <= &2 / log(&2) * x pow 2` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; LOG_2_POS] THEN
    MP_TAC LOG_2_RATIONAL_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A lower bound on H: ln 2 lg x lg(1-x) <= H(x).                            *)
(* ------------------------------------------------------------------------- *)

let BINARY_ENTROPY_RPOW = prove
 (`!x. &0 <= x /\ x <= &1
       ==> binary_entropy x =
           --(log(x rpow x * (&1 - x) rpow (&1 - x)) / log(&2))`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; RPOW_ZERO; REAL_SUB_RZERO; RPOW_ONE;
                    REAL_MUL_LID; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &1` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; RPOW_ZERO; REAL_SUB_REFL; RPOW_ONE;
                    REAL_MUL_RID; LOG_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ &0 < &1 - x` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; RPOW_POS_LT; LOG_RPOW; binary_entropy] THEN
  REAL_ARITH_TAC);;

let BINARY_ENTROPY_GE_LOG_MUL_LOG = prove
 (`!x. &0 <= x /\ x <= &1
       ==> log(&2) * (log x / log(&2)) * (log(&1 - x) / log(&2))
           <= binary_entropy x`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_SUB_RZERO; LOG_1; real_div;
                    REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &1` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_SUB_REFL; LOG_1; real_div;
                    REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[binary_entropy] THEN
  SUBGOAL_THEN
   `log(&2) * (log x / log(&2)) * (log(&1 - x) / log(&2)) =
    (log x * log(&1 - x)) / log(&2)` SUBST1_TAC THENL
   [MP_TAC LOG_2_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; LOG_2_POS] THEN
  MP_TAC(SPEC `x - &1` LOG_RATIONAL_BOUNDS) THEN
  MP_TAC(SPEC `--(x:real)` LOG_RATIONAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_sub; REAL_ARITH `&1 + x - &1 = x`] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `log x <= &0 /\ log(&1 - x) <= &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(x * log x) <= &1 - x /\ --((&1 - x) * log(&1 - x)) <= x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x - &1) / x <= log x` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `--x / (&1 - x) <= log (&1 - x)` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(x * log x) * --log(&1 - x) <= (&1 - x) * --log(&1 - x) /\
                --((&1 - x) * log(&1 - x)) * --log x <= x * --log x`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let BINARY_ENTROPY_LOWER_INEQUALITY = prove
 (`!x. &0 <= x /\ x <= &1
       ==> &4 * x * (&1 - x) <= binary_entropy x /\
           log(&2) * (log x / log(&2)) * (log(&1 - x) / log(&2))
           <= binary_entropy x`,
  SIMP_TAC[BINARY_ENTROPY_GE_QUADRATIC; BINARY_ENTROPY_GE_LOG_MUL_LOG]);;

(* ------------------------------------------------------------------------- *)
(* Tails, for k <= an: sum_{i<=k} C(n,i) <= (1-a)/(1-2a) C(n,k), and the     *)
(* sum is at most 2^(n H(a)) and at most 2^n exp(-2n(1/2 - a)^2).            *)
(* ------------------------------------------------------------------------- *)

let SUM_BINOM_LE_RATIO_MUL = prove
 (`!n k a. &0 <= a /\ a < &1 / &2 /\ &k <= a * &n
           ==> sum(0..k) (\i. &(binom(n,i)))
               <= (&1 - a) / (&1 - &2 * a) * &(binom(n,k))`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; BINOM_REFL; binom; REAL_MUL_RID] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `a < &1 / &2 ==> &0 < &1 - &2 * a`;
             ASSUME `a < &1 / &2`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&(SUC k)` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `&k + &1 < &n` ASSUME_TAC THENL
   [UNDISCH_TAC `&(SUC k) <= a * &n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `a * &n <= &1 / &2 * &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&k + &1) * &(binom(n,SUC k)) = (&n - &k) * &(binom(n,k))`
  MP_TAC THENL
   [MP_TAC(SPECL [`n:num`; `k:num`] BINOM_BOTTOM_STEP) THEN
    REWRITE_TAC[GSYM ADD1; GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&(n - k) = &n - &k` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC];
    ALL_TAC] THEN
  MP_TAC(SPEC `binom(n,k)` REAL_POS) THEN
  MP_TAC(SPEC `binom(n,SUC k)` REAL_POS) THEN
  SPEC_TAC(`&(binom(n,k))`, `b0:real`) THEN
  SPEC_TAC(`&(binom(n,SUC k))`, `b1:real`) THEN
  SPEC_TAC(`sum (0..k) (\i. &(binom (n,i)))`, `s:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&1 - a) * b0 <= a * b1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &n - &k` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&n - &k) * ((&1 - a) * b0) <= (&n - &k) * (a * b1)`
    MP_TAC THENL
     [SUBGOAL_THEN `(&n - &k) * ((&1 - a) * b0) = ((&1 - a) * (&k + &1)) * b1`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(&k + &1) * b1 = (&n - &k) * b0` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&(SUC k) <= a * &n` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&1 - a) / (&1 - &2 * a) * b0 + b1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - &2 * a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - a) / (&1 - &2 * a) * b0 + b1 =
    ((&1 - a) * b0 + (&1 - &2 * a) * b1) / (&1 - &2 * a) /\
    (&1 - a) / (&1 - &2 * a) * b1 = ((&1 - a) * b1) / (&1 - &2 * a)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < &1 - &2 * a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC);;

let SUM_BINOM_MUL_EXP_ENTROPY_LE = prove
 (`!n k a. &0 < a /\ a <= &1 / &2 /\ &k <= a * &n
           ==> sum(0..k) (\i. &(binom(n,i))) *
               exp(&n * (a * log a + (&1 - a) * log(&1 - a))) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k <= (n:num)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `a * &n <= &1 * &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `a:real`; `&1 - a`] REAL_BINOMIAL_THEOREM) THEN
  REWRITE_TAC[REAL_ARITH `a + &1 - a = &1`; REAL_POW_ONE] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..k) (\i. &(binom(n,i)) * a pow i * (&1 - a) pow (n - i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_DIFF] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a pow i * (&1 - a) pow (n - i) =
                exp(&i * log a + &(n - i) * log(&1 - a))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_ADD; REAL_EXP_N; EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `&(n - i) = &n - &i` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log a <= log(&1 - a)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&i <= a * &n` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&k` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (a * &n - &i) * (log(&1 - a) - log a)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SUM_BINOM_LE_ENTROPY = prove
 (`!n k a. a <= &1 / &2 /\ &k <= a * &n
           ==> sum(0..k) (\i. &(binom(n,i)))
               <= &2 rpow (&n * binary_entropy a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < a` THENL
   [ALL_TAC;
    SUBGOAL_THEN `k = 0 /\ a * &n = &0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `a * &n <= &0` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a * n <= &0 <=> &0 <= --a * n`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&k = &0` MP_TAC THENL
       [MP_TAC(SPEC `k:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` REAL_POS) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG; binom] THEN
    SUBGOAL_THEN `&n * binary_entropy a = &0` SUBST1_TAC THENL
     [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      SUBGOAL_THEN `a = &0` SUBST1_TAC THENL
       [UNDISCH_TAC `a * &n = &0` THEN
        ASM_REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ];
        REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_MUL_RZERO]];
      REWRITE_TAC[RPOW_0; REAL_LE_REFL]]] THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `a:real`] SUM_BINOM_MUL_EXP_ENTROPY_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_EXP_POS_LT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_EXP_NEG] THEN
  REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`; binary_entropy] THEN
  SUBGOAL_THEN `~(log(&2) = &0)` MP_TAC THENL
   [MP_TAC LOG_2_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_FIELD `~(l = &0) ==> (n * --x / l) * l = --(n * x)`] THEN
  REWRITE_TAC[REAL_LE_REFL]);;

let SUM_BINOM_LE_EXP_SQUARE = prove
 (`!n k a. a <= &1 / &2 /\ &k <= a * &n
           ==> sum(0..k) (\i. &(binom(n,i)))
               <= &2 pow n * exp(--(&2 * &n * (&1 / &2 - a) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `k:num`; `a:real`] SUM_BINOM_LE_ENTROPY) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> s <= b ==> s <= c`) THEN
  ASM_CASES_TAC `&0 <= a` THENL
   [REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `&2 pow n = exp(&n * log(&2))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_EXP_N] THEN SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    MP_TAC(SPEC `&1 / &2 - a` BINARY_ENTROPY_QUADRATIC_INEQUALITY_GEN) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 / &2 - (&1 / &2 - a) = a`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(&n * log(&2)) * binary_entropy a <=
      (&n * log(&2)) * (&1 - &2 / log(&2) * (&1 / &2 - a) pow 2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; LOG_2_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&n * log(&2)) * (&1 - &2 / log(&2) * (&1 / &2 - a) pow 2) =
      &n * log(&2) - &2 * &n * (&1 / &2 - a) pow 2` SUBST1_TAC THENL
     [MP_TAC LOG_2_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < --a * &n` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `k:num` REAL_POS) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_LZERO; RPOW_0; real_pow; REAL_MUL_RZERO;
                REAL_NEG_0; REAL_EXP_0] THEN
    REAL_ARITH_TAC]);;

let BINOM_TAIL_INEQUALITY = prove
 (`!n k a. &0 <= a /\ a < &1 / &2 /\ &k <= a * &n
           ==> sum(0..k) (\i. &(binom(n,i)))
                 <= (&1 - a) / (&1 - &2 * a) * &(binom(n,k)) /\
               sum(0..k) (\i. &(binom(n,i)))
                 <= &2 rpow (&n * binary_entropy a) /\
               sum(0..k) (\i. &(binom(n,i)))
                 <= &2 pow n * exp(--(&2 * &n * (&1 / &2 - a) pow 2))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUM_BINOM_LE_RATIO_MUL;
    MATCH_MP_TAC SUM_BINOM_LE_ENTROPY;
    MATCH_MP_TAC SUM_BINOM_LE_EXP_SQUARE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The upper bound H(x) <= lg x lg(1-x), via the tangent of x/(-ln(1-x))    *)
(* at 1/2.                                                                   *)
(* ------------------------------------------------------------------------- *)

let TANGENT_LOG_DERIVATIVE_1 = prove
 (`!p q y. y < &1
           ==> ((\x. (p + q * (x - &1 / &2)) * --log(&1 - x) - x)
                has_real_derivative
                (q * --log(&1 - y) + (p + q * (y - &1 / &2)) / (&1 - y) - &1))
               (atreal y)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `y < &1` THEN CONV_TAC REAL_FIELD);;

let TANGENT_LOG_DERIVATIVE_2 = prove
 (`!p q y. y < &1
           ==> ((\x. q * --log(&1 - x) +
                     (p + q * (x - &1 / &2)) / (&1 - x) - &1)
                has_real_derivative
                ((p + q * (&3 / &2 - y)) / (&1 - y) pow 2))
               (atreal y)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  UNDISCH_TAC `y < &1` THEN CONV_TAC REAL_FIELD);;

let TANGENT_LOG_NONNEG = prove
 (`!p q x. p * log(&2) = &1 / &2 /\ q * log(&2) + &2 * p = &1 /\
           &0 <= x /\ x < &1
           ==> &0 <= (p + q * (x - &1 / &2)) * --log(&1 - x) - x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q < &0 /\ &0 < p + q` STRIP_ASSUME_TAC THENL
   [MP_TAC LOG_2_RATIONAL_BOUNDS THEN MP_TAC LOG_2_POS THEN
    DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN
     `p = &1 / (&2 * log(&2)) /\ q = (log(&2) - &1) / log(&2) pow 2`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `q * log(&2) + &2 * p = &1` THEN
      UNDISCH_TAC `p * log(&2) = &1 / &2` THEN UNDISCH_TAC `&0 < log(&2)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; real_div;
                  GSYM REAL_MUL_LNEG] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `&1 / (&2 * log(&2)) + (log(&2) - &1) / log(&2) pow 2 =
        (&3 * log(&2) - &2) / (&2 * log(&2) pow 2)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 - &1 / &2) = --log(&2)` ASSUME_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &2`; LOG_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ff = \x. (p + q * (x - &1 / &2)) * --log(&1 - x) - x` THEN
  ABBREV_TAC
   `ff' = \y. q * --log(&1 - y) + (p + q * (y - &1 / &2)) / (&1 - y) - &1` THEN
  SUBGOAL_THEN `!y. y < &1 ==> (ff has_real_derivative ff' y) (atreal y)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ff"; "ff'"] THEN
    REWRITE_TAC[TANGENT_LOG_DERIVATIVE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y < &1 ==> (ff' has_real_derivative
                   ((p + q * (&3 / &2 - y)) / (&1 - y) pow 2)) (atreal y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "ff'" THEN REWRITE_TAC[TANGENT_LOG_DERIVATIVE_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(ff:real->real) (&1 / &2) = &0 /\ (ff':real->real) (&1 / &2) = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ff"; "ff'"] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real->real) (&0) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[REAL_SUB_RZERO; LOG_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p + q * (x - &1 / &2)) * --log(&1 - x) - x = (ff:real->real) x`
  SUBST1_TAC THENL [EXPAND_TAC "ff" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y < &1
                  ==> (&0 <= (p + q * (&3 / &2 - y)) / (&1 - y) pow 2 <=>
                       &0 <= p + q * (&3 / &2 - y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (&1 - y) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO;
             ASSUME `&0 < (&1 - y) pow 2`];
    ALL_TAC] THEN
  ASM_CASES_TAC `x <= &1 / &2` THENL
   [SUBGOAL_THEN
     `!u v. u IN real_interval[&0,&1 / &2] /\ v IN real_interval[&0,&1 / &2] /\
            u <= v /\ (ff':real->real) u < &0 ==> ff' v <= &0`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`ff':real->real`;
                     `\y. (p + q * (&3 / &2 - y)) / (&1 - y) pow 2`;
                     `real_interval[&0,&1 / &2]`]
                    REAL_DERIVATIVE_SIGN_CHANGE_LE_MAX) THEN
      REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN
          MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
        RULE_ASSUM_TAC BETA_RULE THEN BETA_TAC THEN
        MP_TAC(SPEC `b:real` (ASSUME `!y. y < &1
           ==> (&0 <= (p + q * (&3 / &2 - y)) / (&1 - y) pow 2 <=>
                &0 <= p + q * (&3 / &2 - y))`)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        MP_TAC(SPEC `a:real` (ASSUME `!y. y < &1
           ==> (&0 <= (p + q * (&3 / &2 - y)) / (&1 - y) pow 2 <=>
                &0 <= p + q * (&3 / &2 - y))`)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(fun th ->
          UNDISCH_TAC `&0 < (p + q * (&3 / &2 - a)) / (&1 - a) pow 2` THEN
          DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
          REWRITE_TAC[th]) THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `&0 <= q * (a - b)` MP_TAC THENL
         [ONCE_REWRITE_TAC[REAL_ARITH
            `(q:real) * (a - b) = --q * (b - a)`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        DISCH_THEN(MP_TAC o SPECL [`u:real`; `v:real`; `&1 / &2`]) THEN
        ANTS_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ff:real->real`; `ff':real->real`;
                   `real_interval[&0,&1 / &2]`]
                  REAL_DERIVATIVE_SIGN_CHANGE_MIN_LE) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN(MP_TAC o SPECL [`&0`; `x:real`; `&1 / &2`]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &1 / &2 <= t /\ t < &1 ==> &0 <= (ff':real->real) t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ff':real->real`;
                   `\y. (p + q * (&3 / &2 - y)) / (&1 - y) pow 2`;
                   `real_interval[&1 / &2,t]`; `&1 / &2`; `t:real`]
                  HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      BETA_TAC THEN
      MP_TAC(SPEC `s:real` (ASSUME `!y. y < &1
         ==> (&0 <= (p + q * (&3 / &2 - y)) / (&1 - y) pow 2 <=>
              &0 <= p + q * (&3 / &2 - y))`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `&0 <= --q * (s - &1 / &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:real->real`; `ff':real->real`;
                 `real_interval[&1 / &2,x]`; `&1 / &2`; `x:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_LE_LOG_MUL_LOG = prove
 (`!x. &0 <= x /\ x <= &1
       ==> binary_entropy x <= log x / log(&2) * log(&1 - x) / log(&2)`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_SUB_RZERO; LOG_1; real_div;
                    REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &1` THENL
   [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_SUB_REFL; LOG_1; real_div;
                    REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC LOG_2_RATIONAL_BOUNDS THEN MP_TAC LOG_2_POS THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. &0 <= y /\ y < &1
        ==> y <= (&1 / (&2 * log(&2)) +
                  (log(&2) - &1) / log(&2) pow 2 * (y - &1 / &2)) *
                 --log(&1 - y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`&1 / (&2 * log(&2))`; `(log(&2) - &1) / log(&2) pow 2`;
                  `y:real`] TANGENT_LOG_NONNEG) THEN
    ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - x`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x - &1` LOG_RATIONAL_BOUNDS) THEN
  MP_TAC(SPEC `--(x:real)` LOG_RATIONAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_sub; REAL_ARITH `&1 + x - &1 = x`] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `log x < &0 /\ log(&1 - x) < &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[binary_entropy] THEN
  SUBGOAL_THEN
   `--(x * log x + (&1 - x) * log(&1 - x)) / log(&2) =
    (--(x * log x + (&1 - x) * log(&1 - x)) * log(&2)) / log(&2) pow 2 /\
    log x / log(&2) * log(&1 - x) / log(&2) =
    (log x * log(&1 - x)) / log(&2) pow 2` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT; ASSUME `&0 < log(&2)`] THEN
  SUBGOAL_THEN `&1 / (&2 * log(&2)) * log(&2) = &1 / &2` MP_TAC THENL
   [UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `x <=
    (&1 / (&2 * log (&2)) +
     (log (&2) - &1) / log (&2) pow 2 * (x - &1 / &2)) * --log (&1 - x)` THEN
  UNDISCH_TAC `&1 - x <=
    (&1 / (&2 * log (&2)) +
     (log (&2) - &1) / log (&2) pow 2 * (&1 - x - &1 / &2)) * --log x` THEN
  SPEC_TAC(`&1 / (&2 * log(&2))`, `p:real`) THEN
  SPEC_TAC(`(log(&2) - &1) / log(&2) pow 2`, `q:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `x * --log x <= ((p + q * (x - &1 / &2)) * --log(&1 - x)) * --log x /\
    (&1 - x) * --log(&1 - x) <=
    ((p + q * (&1 - x - &1 / &2)) * --log x) * --log(&1 - x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(x * log x + (&1 - x) * log(&1 - x)) <=
                &2 * p * (log x * log(&1 - x))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(x * log x + (&1 - x) * log(&1 - x)) * log(&2) <=
                (&2 * p * (log x * log(&1 - x))) * log(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * p * (log x * log(&1 - x))) * log(&2) =
                &2 * (p * log(&2)) * (log x * log(&1 - x))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An upper bound on H: H(x) <= (4x(1-x))^(1/ln 4), from                     *)
(* (1-s^2) L(s) >= 2s H((1-s)/2) on [0,1).                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_1 = prove
 (`!c s. abs s < &1
         ==> ((\s. (&1 - s pow 2) * (log(&1 + s) - log(&1 - s)) - &2 * s +
                   &2 * c * s *
                   ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s)))
              has_real_derivative
              (&2 * c * ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s)) -
               &2 * (&1 - c) * s * (log(&1 + s) - log(&1 - s)))) (atreal s)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  SUBGOAL_THEN `(&1 + s) * inv(&1 + s) = &1 /\ (&1 - s) * inv(&1 - s) = &1`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RING]);;

let HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_2 = prove
 (`!c s. abs s < &1
         ==> ((\s. &2 * c *
                   ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s)) -
                   &2 * (&1 - c) * s * (log(&1 + s) - log(&1 - s)))
              has_real_derivative
              (&2 * (&2 * c - &1) * (log(&1 + s) - log(&1 - s)) -
               &4 * (&1 - c) * s / (&1 - s pow 2))) (atreal s)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + s) * inv(&1 + s) = &1 /\ (&1 - s) * inv(&1 - s) = &1 /\
                (&1 - s pow 2) * inv(&1 - s pow 2) = &1`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    REWRITE_TAC[REAL_ARITH `&1 - s pow 2 = (&1 - s) * (&1 + s)`;
                REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING]);;

let HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_3 = prove
 (`!c s. abs s < &1
         ==> ((\s. &2 * (&2 * c - &1) * (log(&1 + s) - log(&1 - s)) -
                   &4 * (&1 - c) * s / (&1 - s pow 2))
              has_real_derivative
              (&4 * ((&3 * c - &2) - c * s pow 2) / (&1 - s pow 2) pow 2))
             (atreal s)`,
  REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
  SUBGOAL_THEN `~(&1 - s pow 2 = &0) /\ ~(&1 + s = &0) /\ ~(&1 - s = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&1 - s pow 2 = (&1 - s) * (&1 + s)`;
                REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let BINARY_ENTROPY_HALF_SUB_EXPAND = prove
 (`!s. abs s <= &1
       ==> binary_entropy((&1 - s) / &2) =
           &1 - ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s)) /
                (&2 * log(&2))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `abs s = &1` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (REAL_ARITH `abs s = &1 ==> s = &1 \/ s = -- &1`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[BINARY_ENTROPY_0_1; REAL_MUL_LZERO; REAL_ADD_LID;
                REAL_ADD_RID] THEN
    MP_TAC LOG_2_POS THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[binary_entropy] THEN
  SUBGOAL_THEN `&1 - (&1 - s) / &2 = (&1 + s) / &2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - s /\ &0 < &1 + s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &2`] THEN
  MP_TAC LOG_2_POS THEN CONV_TAC REAL_FIELD);;

let BINARY_ENTROPY_LE_SQRT = prove
 (`!x. &0 < x /\ x <= &1 ==> binary_entropy x <= &3 * (x + sqrt x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` BINARY_ENTROPY_LE_MUL_LOG) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 < sqrt x /\ sqrt x pow 2 = x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `sqrt x - &1` LOG_RATIONAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 + s - &1 = s`] THEN
  ASM_SIMP_TAC[LOG_SQRT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x * --log x <= &2 * sqrt x - &2 * x` ASSUME_TAC THENL
   [UNDISCH_TAC `(sqrt x - &1) / sqrt x <= log x / &2` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `sqrt x * ((sqrt x - &1) * &2) <= sqrt x * (log x / &2 * sqrt x * &2)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt x * ((sqrt x - &1) * &2) = &2 * x - &2 * sqrt x /\
                  sqrt x * (log x / &2 * sqrt x * &2) = x * log x`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `sqrt x pow 2 = x` THEN CONV_TAC REAL_RING;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(x:real) * a / l = (x * a) / l`] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; LOG_2_POS] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &4`] THEN
  SUBGOAL_THEN `log(&4) = &2 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&56 / &81 * sqrt x <= log(&2) * sqrt x /\
                &0 <= x * log(&2)` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[LOG_2_RATIONAL_BOUNDS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC LOG_2_POS THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let BINARY_ENTROPY_HALF_MUL_LE_LOG_RATIO = prove
 (`!s. &0 <= s /\ s < &1
       ==> &2 * s * binary_entropy((&1 - s) / &2)
           <= (&1 - s pow 2) * (log(&1 + s) - log(&1 - s))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = &1 / (&2 * log(&2))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC LOG_2_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs t < &1 ==> binary_entropy((&1 - t) / &2) =
                  &1 - c * ((&1 + t) * log(&1 + t) + (&1 - t) * log(&1 - t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BINARY_ENTROPY_HALF_SUB_EXPAND; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p0 = \s. (&1 - s pow 2) * (log(&1 + s) - log(&1 - s)) -
                       &2 * s + &2 * c * s *
                       ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s))` THEN
  ABBREV_TAC `p1 = \s. &2 * c *
                       ((&1 + s) * log(&1 + s) + (&1 - s) * log(&1 - s)) -
                       &2 * (&1 - c) * s * (log(&1 + s) - log(&1 - s))` THEN
  ABBREV_TAC `p2 = \s. &2 * (&2 * c - &1) * (log(&1 + s) - log(&1 - s)) -
                       &4 * (&1 - c) * s / (&1 - s pow 2)` THEN
  ABBREV_TAC `p3 = \s. &4 * ((&3 * c - &2) - c * s pow 2) /
                       (&1 - s pow 2) pow 2` THEN
  SUBGOAL_THEN
   `(!s. &0 <= s /\ s < &1 ==> (p0 has_real_derivative p1 s) (atreal s)) /\
    (!s. &0 <= s /\ s < &1 ==> (p1 has_real_derivative p2 s) (atreal s)) /\
    (!s. &0 <= s /\ s < &1 ==> (p2 has_real_derivative p3 s) (atreal s))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p0"; "p1"; "p2"; "p3"] THEN REPEAT CONJ_TAC THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_1;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_2;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG_RATIO_ENTROPY_3] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s. &0 <= s /\ s < &1
         ==> (p1 has_real_derivative p2 s)
             (atreal s within {x | &0 <= x /\ x < &1})) /\
    (!s. &0 <= s /\ s < &1
         ==> (p2 has_real_derivative p3 s)
             (atreal s within {x | &0 <= x /\ x < &1}))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]; ALL_TAC] THEN
  SUBGOAL_THEN `(p0:real->real) (&0) = &0 /\ (p1:real->real) (&0) = &0 /\
                (p2:real->real) (&0) = &0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p0"; "p1"; "p2"] THEN
    REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO; LOG_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. &0 <= u /\ u <= v /\ v < &1 /\ (p3:real->real) u < &0
          ==> p3 v <= &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "p3" THEN BETA_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&3 * c - &2 - c * u pow 2 < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC
       `&4 * (&3 * c - &2 - c * u pow 2) / (&1 - u pow 2) pow 2 < &0` THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real) * u pow 2 <= c * v pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
    REWRITE_TAC[real_div; REAL_ARITH `--(&4 * a * b) = &4 * --a * b`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `is_realinterval {x:real | &0 <= x /\ x < &1}` ASSUME_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g g'. (!s. &0 <= s /\ s < &1
                ==> (g has_real_derivative g' s)
                    (atreal s within {x | &0 <= x /\ x < &1})) /\
           &0 <= g(&0) /\
           (!u v. &0 <= u /\ u <= v /\ v < &1 /\ g' u < &0 ==> g' v <= &0)
           ==> !u v. &0 <= u /\ u <= v /\ v < &1 /\ g u < &0 ==> g v <= &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real->real`; `g':real->real`;
                   `{x:real | &0 <= x /\ x < &1}`]
                  REAL_DERIVATIVE_SIGN_CHANGE_MIN_LE) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `u:real`; `v:real`]) THEN
    ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p2:real->real`; `p3:real->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`p1:real->real`; `p2:real->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= (p0:real->real) s` MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "p0" THEN
    MP_TAC(SPEC `s:real` (ASSUME `!t. abs t < &1
      ==> binary_entropy ((&1 - t) / &2) =
          &1 - c * ((&1 + t) * log (&1 + t) + (&1 - t) * log (&1 - t))`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. s <= t /\ t < &1 ==> (p0:real->real) t <= p0 s`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p0:real->real`; `p1:real->real`;
                   `{x:real | &0 <= x /\ x < &1}`]
                  REAL_DERIVATIVE_SIGN_CHANGE_MIN_LE) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `s:real`; `t:real`]) THEN
    ANTS_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = --((p0:real->real) s) / &24` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = min ((&1 - s) / &2) (d pow 2)` THEN
  SUBGOAL_THEN `&0 < x /\ x <= (&1 - s) / &2 /\ x <= d pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt x <= d /\ x <= sqrt x` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(d pow 2) = d` (fun th -> CONJ_TAC THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN
       MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC]) THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt x /\ sqrt x pow 2 = x /\ sqrt x <= &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt x * sqrt x <= sqrt x * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `sqrt x pow 2 = x` THEN REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - &2 * x` o check (fun th ->
    can (find_term ((=) `(p0:real->real) s`)) (concl th) &&
    is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&1 - &2 * x` (ASSUME `!t. abs t < &1
      ==> binary_entropy ((&1 - t) / &2) =
          &1 - c * ((&1 + t) * log (&1 + t) + (&1 - t) * log (&1 - t))`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - (&1 - &2 * x)) / &2 = x`] THEN
  ABBREV_TAC `t = &1 - &2 * x` THEN
  ABBREV_TAC `kk = (&1 + t) * log(&1 + t) + (&1 - t) * log(&1 - t)` THEN
  ABBREV_TAC `ll = log(&1 + t) - log(&1 - t)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(p0:real->real) t = (&1 - t pow 2) * ll - &2 * t * binary_entropy x`
  SUBST1_TAC THENL
   [EXPAND_TAC "p0" THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= binary_entropy x /\ binary_entropy x <= &6 * d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `x:real` BINARY_ENTROPY_GE_QUADRATIC) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a <= b ==> &0 <= b`) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `x:real` BINARY_ENTROPY_LE_SQRT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - t pow 2) * ll` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ll" THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * binary_entropy x <= &1 * (&6 * d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_HALF_LE_RPOW = prove
 (`!s. &0 <= s /\ s < &1
       ==> binary_entropy((&1 - s) / &2)
           <= (&1 - s pow 2) rpow (&1 / (&2 * log(&2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = &1 / (&2 * log(&2))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC LOG_2_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs t < &1 ==> binary_entropy((&1 - t) / &2) =
                  &1 - c * ((&1 + t) * log(&1 + t) + (&1 - t) * log(&1 - t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[BINARY_ENTROPY_HALF_SUB_EXPAND; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < &1
        ==> &0 < binary_entropy((&1 - t) / &2) /\ &0 < &1 - t pow 2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &1 - t pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(&1 - t) / &2` BINARY_ENTROPY_GE_QUADRATIC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= b ==> &0 < b`) THEN
    REWRITE_TAC[REAL_ARITH `&4 * (&1 - t) / &2 * (&1 - (&1 - t) / &2) =
                            &1 - t pow 2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `s:real` (ASSUME `!t. &0 <= t /\ t < &1
     ==> &0 < binary_entropy((&1 - t) / &2) /\ &0 < &1 - t pow 2`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[rpow] THEN
  SUBGOAL_THEN `binary_entropy((&1 - s) / &2) =
                exp(log(binary_entropy((&1 - s) / &2)))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MP_TAC(SPEC `s:real` (ASSUME `!t. abs t < &1
      ==> binary_entropy ((&1 - t) / &2) =
          &1 - c * ((&1 + t) * log (&1 + t) + (&1 - t) * log (&1 - t))`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
   [`\t. c * log(&1 - t pow 2) -
         log(&1 - c * ((&1 + t) * log(&1 + t) + (&1 - t) * log(&1 - t)))`;
    `\t. c * ((&1 - t pow 2) * (log(&1 + t) - log(&1 - t)) -
              &2 * t * (&1 - c * ((&1 + t) * log(&1 + t) +
                                  (&1 - t) * log(&1 - t)))) /
         ((&1 - t pow 2) *
          (&1 - c * ((&1 + t) * log(&1 + t) + (&1 - t) * log(&1 - t))))`;
    `real_interval[&0,s]`; `&0`; `s:real`]
   HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO; LOG_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LOG_1; REAL_MUL_RZERO; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  (MP_TAC(SPEC `t:real` (ASSUME `!t. &0 <= t /\ t < &1
     ==> &0 < binary_entropy((&1 - t) / &2) /\ &0 < &1 - t pow 2`)) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `t:real` BINARY_ENTROPY_HALF_MUL_LE_LOG_RATIO) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `t:real` (ASSUME `!t. abs t < &1
       ==> binary_entropy ((&1 - t) / &2) =
           &1 - c * ((&1 + t) * log (&1 + t) + (&1 - t) * log (&1 - t))`)) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   REPEAT STRIP_TAC) THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    UNDISCH_TAC
     `&0 < &1 - c * ((&1 + t) * log (&1 + t) + (&1 - t) * log (&1 - t))` THEN
    UNDISCH_TAC `&0 < &1 - t pow 2` THEN
    SUBGOAL_THEN `~(&1 + t = &0) /\ ~(&1 - t = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`log(&1 + t)`, `p:real`) THEN
    SPEC_TAC(`log(&1 - t)`, `q:real`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `~(&1 - t pow 2 = &0) /\
                  ~(&1 - c * ((&1 + t) * p + (&1 - t) * q) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(&1 + t = &0)` THEN UNDISCH_TAC `~(&1 - t = &0)` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let BINARY_ENTROPY_LE_RPOW = prove
 (`!x. &0 <= x /\ x <= &1
       ==> binary_entropy x <= (&4 * x * (&1 - x)) rpow (&1 / log(&4))`,
  SUBGOAL_THEN `log(&4) = &2 * log(&2)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= x /\ x <= &1 / &2
                    ==> binary_entropy x <=
                        (&4 * x * (&1 - x)) rpow (&1 / (&2 * log(&2)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[BINARY_ENTROPY_0_1] THEN MATCH_MP_TAC RPOW_POS_LE THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `&1 - &2 * x` BINARY_ENTROPY_HALF_LE_RPOW) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - (&1 - &2 * x)) / &2 = x`;
                REAL_ARITH `&1 - (&1 - &2 * x) pow 2 = &4 * x * (&1 - x)`];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= &1 / &2` THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM BINARY_ENTROPY_SYM] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&4 * x * (&1 - x) =
                               &4 * (&1 - x) * (&1 - (&1 - x))`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let BINARY_ENTROPY_UPPER_INEQUALITY = prove
 (`!x. &0 <= x /\ x <= &1
       ==> binary_entropy x <= x * log(&4 / x) / log(&2) /\
           binary_entropy x <= (&1 - x) * log(&4 / (&1 - x)) / log(&2) /\
           binary_entropy x <= (&4 * x * (&1 - x)) rpow (&1 / log(&4)) /\
           binary_entropy x <= log x / log(&2) * log(&1 - x) / log(&2)`,
  SIMP_TAC[BINARY_ENTROPY_LE_MUL_LOG; BINARY_ENTROPY_LE_MUL_LOG_ALT;
           BINARY_ENTROPY_LE_RPOW; BINARY_ENTROPY_LE_LOG_MUL_LOG]);;
