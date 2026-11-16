(* ========================================================================= *)
(* Maximal inequalities and the probabilistic method: Kolmogorov, Etemadi,   *)
(* Doob, Gauss, the Lovasz local lemma, Harris and Janson, from L. Kozma,    *)
(* "Useful Inequalities" (v0.44).                                            *)
(* ========================================================================= *)

needs "kozma/probability_concentration.ml";;

(* ------------------------------------------------------------------------- *)
(* Independent families of events (every nonempty finite subfamily has       *)
(* probability of the intersection equal to the product), an event mutually  *)
(* independent of a family of events (the event is independent of every      *)
(* intersection of a nonempty finite subfamily), and unimodality about m in  *)
(* Khinchin's sense: the CDF is convex on (-inf,m) and concave on (m,inf),   *)
(* an atom at m allowed.                                                     *)
(* ------------------------------------------------------------------------- *)

let indep_event_family = new_definition
 `indep_event_family (p:A prob_space) (s:K->bool) (E:K->A->bool) <=>
  (!i. i IN s ==> E i IN prob_events p) /\
  (!u. u SUBSET s /\ FINITE u /\ ~(u = {})
       ==> prob p (INTERS (IMAGE E u)) = product u (\i. prob p (E i)))`;;

let event_mutually_indep = new_definition
 `event_mutually_indep (p:A prob_space) (a:A->bool) (s:K->bool)
                       (E:K->A->bool) <=>
  a IN prob_events p /\
  (!i. i IN s ==> E i IN prob_events p) /\
  (!u. u SUBSET s /\ FINITE u /\ ~(u = {})
       ==> prob p (a INTER INTERS (IMAGE E u)) =
           prob p a * prob p (INTERS (IMAGE E u)))`;;

let unimodal_about = new_definition
 `unimodal_about (p:A prob_space) (X:A->real) (m:real) <=>
  random_variable p X /\
  cdf p X real_convex_on {x | x < m} /\
  (\x. --cdf p X x) real_convex_on {x | m < x}`;;

(* ------------------------------------------------------------------------- *)
(* Gauss's inequality for a distribution unimodal about m, with tau^2 = E[(X *)
(* - m)^2]: Pr[|X - m| >= e] <= 4 tau^2 / (9 e^2) for every e > 0, and Pr[|X *)
(* - m| >= e] <= 1 - e / (sqrt 3 tau) for e <= 2 tau / sqrt 3. The function  *)
(* G(y) = Pr[X - m > y] + Pr[X - m <= -y] is convex on (0,inf) and its grid  *)
(* sums sum_k (y_k^2 - y_(k-1)^2) G(y_k) are at most the second moment; the  *)
(* bound is then a fact about convex functions.                              *)
(* ------------------------------------------------------------------------- *)

let SUM_ODD_TIMES_COMPLEMENT = prove
 (`!n. sum(1..n) (\k. (&2 * &k - &1) * (&n - &k)) =
       &n * (&n - &1) * (&2 * &n - &1) / &6`,
  SUBGOAL_THEN `!n. sum(1..n) (\k. &2 * &k - &1) = &n pow 2` ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`;
              GSYM REAL_OF_NUM_SUC] THEN
  REWRITE_TAC[REAL_ARITH `(a:real) * ((n + &1) - k) = a * (n - k) + a`;
              SUM_ADD_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let GRID_SUM_LINE = prove
 (`!a b n.
     &0 < b /\ 1 <= n
     ==> sum(1..n) (\k. ((&k * b / &n) pow 2 - ((&k - &1) * b / &n) pow 2) *
                        (a * (&1 - (&k * b / &n) / b))) =
         a * b pow 2 * (&n - &1) * (&2 * &n - &1) / (&6 * &n pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. (a * b pow 2 / &n pow 3) *
                             ((&2 * &k - &1) * (&n - &k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    UNDISCH_TAC `&0 < &n` THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[SUM_LMUL; SUM_ODD_TIMES_COMPLEMENT] THEN
    UNDISCH_TAC `&0 < &n` THEN CONV_TAC REAL_FIELD]);;

let GRID_BOUND_LIMIT = prove
 (`!c t. &0 <= c /\
         (!n. 1 <= n
              ==> c * (&n - &1) * (&2 * &n - &1) / (&6 * &n pow 2) <= t)
         ==> c / &3 <= t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. 1 <= n ==> c / &3 - c / (&2 * &n) <= t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= t ==> a <= t:real`) THEN
    SUBGOAL_THEN `&1 <= &n` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SPEC_TAC(`&n:real`,`x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `c * (x - &1) * (&2 * x - &1) / (&6 * x pow 2) =
      (c / &3 - c / (&2 * x)) + c / (&6 * x pow 2)`
    SUBST1_TAC THENL [UNDISCH_TAC `&1 <= x` THEN CONV_TAC REAL_FIELD;
                      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> a <= a + y`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `c / (c / &3 - t) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `&0 < c / &3 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
                                                   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c / (c / &3 - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    free_in `(/):real->real->real` (concl th) && is_forall(concl th) &&
    not(free_in `(pow):real->num->real` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c + (c / &3 - t) <= &n * (c / &3 - t)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `c / &3 - t`] REAL_DIV_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o
      LAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[REAL_ARITH `x * d + d = (x + &1) * d`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c / (&2 * &n) < c / &3 - t` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let GAUSS_CUBIC_BOUND = prove
 (`!g b e. &0 <= e /\ &0 <= b /\ &0 <= g
           ==> &27 * g * e pow 2 * (b - e) <= &4 * g * b pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= g * (&2 * b - &3 * e) pow 2 * (b + &3 * e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let GAUSS_CUBIC_MONO = prove
 (`!b c e. &0 < e /\ &3 * e <= &2 * c /\ c <= b
           ==> c pow 3 * (b - e) <= b pow 3 * (c - e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= b - c /\ &0 <= c /\ &0 <= c - e /\ &0 <= &2 * c - &3 * e`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c pow 2 * (&2 * c - &3 * e)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * c * (b - c) + (b - c) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (b - c) * (c pow 2 * (&2 * c - &3 * e) +
                     (c - e) * (&3 * c * (b - c) + (b - c) pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL];
    REAL_ARITH_TAC]);;

let GAUSS_TAIL_BOUND = prove
 (`!G t e.
     G real_convex_on {y | &0 < y} /\
     (!y. &0 < y ==> &0 <= G y /\ G y <= &1) /\
     (!y z. &0 < y /\ y <= z ==> G z <= G y) /\
     (!b n. &0 < b /\ 1 <= n
            ==> sum(1..n) (\k. ((&k * b / &n) pow 2 -
                                ((&k - &1) * b / &n) pow 2) *
                               G(&k * b / &n)) <= t) /\
     &0 < e
     ==> &9 * e pow 2 * G e <= &4 * t /\
         (&3 * e pow 2 <= &4 * t ==> e pow 2 <= &3 * t * (&1 - G e) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b. &0 < b ==> b pow 2 * G b <= t` (LABEL_TAC "one") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`b:real`; `1`]) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    REWRITE_TAC[SUM_SING] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_MUL_LZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
   [USE_THEN "one" (MP_TAC o SPEC `&1`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      not(free_in `t:real` (concl th)))) THEN
    REWRITE_TAC[REAL_LT_01] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real`; `{y | &0 < y}`; `e:real`]
    REAL_CONVEX_ON_SUPPORTING_LINE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`e / &2`; `&2 * e`] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real` (LABEL_TAC "line"))] THEN
  SUBGOAL_THEN `(G:real->real)(&2 * e) <= G e` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      length(fst(strip_forall(concl th))) = 2 &&
      not(free_in `t:real` (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `G e + c * (&2 * e - e) <= G(&2 * e)` ASSUME_TAC THENL
   [USE_THEN "line" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < c * e` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (G:real->real) e /\ G e <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!y. &0 < y ==> &0 <= (G:real->real) y /\ G y <= &1` THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(G:real->real) e = &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = (G:real->real) e` THEN
  SUBGOAL_THEN `&0 < g` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    ABBREV_TAC `b = (t + &1) / g + &1` THEN
    SUBGOAL_THEN `&1 <= b` ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `g <= (G:real->real) b /\ G b <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPEC `b:real` (ASSUME
          `!y. &0 < y ==> g + c * (y - e) <= (G:real->real) y`)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
        MP_TAC(SPEC `b:real` (ASSUME
          `!y. &0 < y ==> &0 <= (G:real->real) y /\ G y <= &1`)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(SPEC `b:real` (ASSUME
      `!b. &0 < b ==> b pow 2 * (G:real->real) b <= t`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `b * g = t + &1 + g` ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `b * g <= b * (b * (G:real->real) b)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
                                                     ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(G:real->real) b` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= (b - &1) * x ==> x <= b * x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `c < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  ABBREV_TAC `d = --c:real` THEN
  SUBGOAL_THEN `&0 < d:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
                                               ALL_TAC] THEN
  ABBREV_TAC `b = e + g / d:real` THEN
  SUBGOAL_THEN `e < b:real /\ d * (b - e) = g:real` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> e < e + x:real`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV];
      REWRITE_TAC[REAL_ARITH `((e:real) + x) - e = x`] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. &0 < y ==> d * (b - y) <= (G:real->real) y`
  (LABEL_TAC "line'") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `y:real` (ASSUME
      `!y. &0 < y ==> g + c * (y - e) <= (G:real->real) y`)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= z ==> y <= z:real`) THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `d * (b - e) = g:real` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `--c = d:real` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d * b <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `y0 = min e ((d * b - &1) / (&2 * d))` THEN
    SUBGOAL_THEN `&0 < y0 /\ y0 <= (d * b - &1) / (&2 * d)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y0" THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `d * y0 <= (d * b - &1) / &2` ASSUME_TAC THENL
     [MP_TAC(SPECL [`d:real`; `y0:real`; `(d * b - &1) / (&2 * d)`]
        REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x = z ==> a <= x ==> a <= z:real`) THEN
      UNDISCH_TAC `&0 < d:real` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(MP (SPEC `y0:real` (ASSUME
      `!y. &0 < y ==> d * (b - y) <= (G:real->real) y`))
      (ASSUME `&0 < y0`)) THEN
    MP_TAC(MP (SPEC `y0:real` (ASSUME
      `!y. &0 < y ==> &0 <= (G:real->real) y /\ G y <= &1`))
      (ASSUME `&0 < y0`)) THEN
    UNDISCH_TAC `d * y0 <= (d * b - &1) / &2` THEN
    UNDISCH_TAC `&1 < d * b` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d * b) * b pow 2 <= &3 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x / &3 <= t ==> x <= &3 * t`) THEN
    MATCH_MP_TAC GRID_BOUND_LIMIT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`d * b:real`; `b:real`; `n:num`] GRID_SUM_LINE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..n) (\k. ((&k * b / &n) pow 2 -
                                ((&k - &1) * b / &n) pow 2) *
                               (G:real->real)(&k * b / &n))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        free_in `sum:(num->bool)->(num->real)->real` (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&0 < &n /\ &1 <= &k` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b / &n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (&k - &1) * b / &n /\ (&k - &1) * b / &n <= &k * b / &n`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `&k * b / &n` (ASSUME
      `!y. &0 < y ==> d * (b - y) <= (G:real->real) y`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= z ==> x <= z:real`) THEN
    UNDISCH_TAC `e < b:real` THEN UNDISCH_TAC `&0 < e` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&9 * e pow 2 * g <= &4 * t` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g:real`; `b:real`; `e:real`] GAUSS_CUBIC_BOUND) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * g * b pow 3 <= (b - e) * &12 * t` MP_TAC THENL
     [FIRST_ASSUM(fun th ->
        if concl th = `d * (b - e) = g:real` then SUBST1_TAC(SYM th)
        else NO_TAC) THEN
      MP_TAC(SPECL [`&4 * (b - e):real`; `(d * b) * (b:real) pow 2`;
                    `&3 * t:real`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(b - e) * (&27 * e pow 2 * g) <= (b - e) * (&12 * t:real)`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b - e:real`
     (fun th -> REWRITE_TAC[MATCH_MP REAL_LE_LMUL_EQ th]) THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&3 * g <= &1` THENL
   [SUBGOAL_THEN `&0 <= t * ((&1 - g) pow 2 - &4 / &9)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(&1 - g) pow 2 - &4 / &9 = ((&1 - g) - &2 / &3) * ((&1 - g) + &2 / &3)`
      SUBST1_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `u = &1 - g:real` THEN
  SUBGOAL_THEN `d * e <= u:real` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    FIRST_ASSUM(fun th ->
      if concl th = `d * (b - e) = g:real` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * e` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL];
                                              ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u /\ &3 * u < &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b0 = e / u:real` THEN
  SUBGOAL_THEN `b0 * u = e:real` ASSUME_TAC THENL
   [EXPAND_TAC "b0" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `e <= u * b:real` ASSUME_TAC THENL
   [SUBGOAL_THEN `(d * b) * (b - e) <= &1 * (b - e:real)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "u" THEN
    FIRST_ASSUM(fun th ->
      if concl th = `d * (b - e) = g:real` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * e <= &2 * b0 /\ b0 <= b:real` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `&0 < u:real`
      then ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]
      else NO_TAC) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `u * &2 * b0 = &2 * e:real` SUBST1_TAC THENL
       [FIRST_ASSUM(fun th ->
          if concl th = `b0 * u = e:real` then SUBST1_TAC(SYM th)
          else NO_TAC) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= e * (&2 - &3 * u)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `g * b0 pow 3 <= &3 * t * (b0 - e:real)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`b:real`; `b0:real`; `e:real`] GAUSS_CUBIC_MONO) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `d * (b0 pow 3 * (b - e)) <= d * (b pow 3 * (b0 - e:real))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
    SUBGOAL_THEN
     `((d * b) * b pow 2) * (b0 - e) <= (&3 * t) * (b0 - e:real)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      if concl th = `d * (b - e) = g:real` then SUBST1_TAC(SYM th)
      else NO_TAC) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `u pow 3 * (g * b0 pow 3) <= u pow 3 * (&3 * t * (b0 - e:real))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `u pow 3 * (g * b0 pow 3) = g * (b0 * u) pow 3 /\
    u pow 3 * (&3 * t * (b0 - e:real)) = &3 * t * u pow 2 * (b0 * u - e * u)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e - e * u = e * g:real` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th ->
      if concl th = `&1 - g = u:real` then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e * g:real`
   (fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]) THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let GRID_INDICATOR_SUM_LE = prove
 (`!h a N.
     &0 <= h /\ &0 <= a
     ==> sum(1..N) (\k. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
                        (if &k * h <= a then &1 else &0)) <= a pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!N. sum(1..N) (\k. (&k * h) pow 2 - ((&k - &1) * h) pow 2) =
        (&N * h) pow 2`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`;
                    GSYM REAL_OF_NUM_SUC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  ASM_CASES_TAC `&(SUC N) * h <= a` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `sum(1..N) (\k. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
                   (if &k * h <= a then &1 else &0)) =
    sum(1..N) (\k. (&k * h) pow 2 - ((&k - &1) * h) pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&k * h <= a` (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(SUC N) * h` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(&N * h) pow 2 + (&(SUC N) * h) pow 2 - ((&(SUC N) - &1) * h) pow 2 =
    (&(SUC N) * h) pow 2`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
                    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]);;

let SQ_LE_FROM_BELOW = prove
 (`!e K. &0 < e /\ (!x. &0 < x /\ x < e ==> x pow 2 <= K) ==> e pow 2 <= K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `K < &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `e / &2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (e:real) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 <= r /\ r < &1 /\ (K:real) = r * (e:real) pow 2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(K:real) / (e:real) pow 2` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e:real) * (&1 + r) / &2`) THEN
  REWRITE_TAC[NOT_IMP; REAL_NOT_LE] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e * x < e * &1
         ==> e * x < e:real`) THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && lhs(concl th) = `K:real` then SUBST1_TAC th
      else NO_TAC) THEN
    SUBGOAL_THEN `&0 < (e:real) pow 2 * (&1 - r) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let UNIMODAL_TAIL_CONVEX = prove
 (`!p:A prob_space X m.
     unimodal_about p X m
     ==> (\y. (&1 - cdf p X (m + y)) + cdf p X (m - y))
         real_convex_on {y | &0 < y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[unimodal_about; real_convex_on;
                                  IN_ELIM_THM] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `u:real`;
                                      `v:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `m + u * x + v * y = u * (m + x) + v * (m + y:real)`
  SUBST1_TAC THENL [UNDISCH_TAC `u + v = &1` THEN CONV_TAC REAL_RING;
                    ALL_TAC] THEN
  SUBGOAL_THEN `m - (u * x + v * y) = u * (m - x) + v * (m - y:real)`
  SUBST1_TAC THENL [UNDISCH_TAC `u + v = &1` THEN CONV_TAC REAL_RING;
                    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m + x:real`; `m + y:real`; `u:real`;
                                `v:real`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m - x:real`; `m - y:real`; `u:real`;
                                `v:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `u + v = &1` THEN ASM_REAL_ARITH_TAC);;

let GRID_TAIL_MOMENT = prove
 (`!p:A prob_space X m h N.
     random_variable p X /\ integrable p (\x. (X x - m) pow 2) /\ &0 <= h
     ==> sum(1..N) (\k. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
                        ((&1 - cdf p X (m + &k * h)) + cdf p X (m - &k * h)))
         <= expectation p (\x. (X x - m) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = \k. prob_carrier p DIFF
                      {x | x IN prob_carrier p /\
                         (X:A->real) x <= m + &k * h}` THEN
  ABBREV_TAC
   `B = \k. {x | x IN prob_carrier p /\ (X:A->real) x <= m - &k * h}` THEN
  SUBGOAL_THEN
   `!k. (A:num->A->bool) k IN prob_events p /\
        (B:num->A->bool) k IN prob_events p`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN
    ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; RV_CDF_EVENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. (&1 - cdf p X (m + &k * h)) + cdf p X (m - &k * h) =
        prob p ((A:num->A->bool) k) + prob p ((B:num->A->bool) k)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN REWRITE_TAC[cdf] THEN
    ASM_SIMP_TAC[PROB_COMPL; RV_CDF_EVENTS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `expectation p (\x. sum(1..N) (\k.
      ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
      (indicator_fn ((A:num->A->bool) k) x +
       indicator_fn ((B:num->A->bool) k) x)))` THEN
  SUBGOAL_THEN
   `!k. integrable p (\x. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
                          (indicator_fn ((A:num->A->bool) k) x +
                           indicator_fn ((B:num->A->bool) k) x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[INTEGRABLE_INDICATOR];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL [`p:A prob_space`; `1..N`;
      `\k x. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
             (indicator_fn ((A:num->A->bool) k) x +
              indicator_fn ((B:num->A->bool) k) x)`]
      EXPECTATION_SUM_FINITE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `(&k * h) pow 2 - ((&k - &1) * h) pow 2`;
                   `\x. indicator_fn ((A:num->A->bool) k) x +
                        indicator_fn ((B:num->A->bool) k) x`]
      EXPECTATION_CMUL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[INTEGRABLE_INDICATOR];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `indicator_fn ((A:num->A->bool) k)`;
                   `indicator_fn ((B:num->A->bool) k)`] EXPECTATION_ADD) THEN
    ASM_SIMP_TAC[INTEGRABLE_INDICATOR; EXPECTATION_INDICATOR];
    ALL_TAC] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUM_FINITE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..N) (\k. ((&k * h) pow 2 - ((&k - &1) * h) pow 2) *
                   (if &k * h <= abs((X:A->real) x - m) then &1 else &0))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(SPECL [`h:real`; `abs((X:A->real) x - m)`; `N:num`]
      GRID_INDICATOR_SUM_LE) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POW2_ABS]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `&1 <= &k` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN
  REWRITE_TAC[indicator_fn; IN_DIFF; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &k * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let GAUSS_TAIL_PROB = prove
 (`!p:A prob_space X m e.
     unimodal_about p X m /\ integrable p (\x. (X x - m) pow 2) /\ &0 < e
     ==> &9 * e pow 2 *
         prob p {x | x IN prob_carrier p /\ abs(X x - m) >= e}
         <= &4 * expectation p (\x. (X x - m) pow 2) /\
         (&3 * e pow 2 <= &4 * expectation p (\x. (X x - m) pow 2)
          ==> e pow 2 <=
              &3 * expectation p (\x. (X x - m) pow 2) *
              (&1 - prob p {x | x IN prob_carrier p /\
                                abs(X x - m) >= e}) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [unimodal_about]) THEN
  ABBREV_TAC `t = expectation p (\x. ((X:A->real) x - m) pow 2)` THEN
  ABBREV_TAC
   `P = prob p {x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e}` THEN
  SUBGOAL_THEN `!a b. a <= b ==> cdf p (X:A->real) a <= cdf p X b`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CDF_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. &0 <= cdf p (X:A->real) a /\ cdf p X a <= &1`
  (LABEL_TAC "bds") THENL
   [GEN_TAC THEN MATCH_MP_TAC CDF_BOUNDS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `G = \y. (&1 - cdf p (X:A->real) (m + y)) + cdf p X (m - y)` THEN
  SUBGOAL_THEN
   `!x. &0 < x
        ==> &9 * x pow 2 * (G:real->real) x <= &4 * t /\
            (&3 * x pow 2 <= &4 * t ==> x pow 2 <= &3 * t * (&1 - G x) pow 2)`
  (LABEL_TAC "core") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC GAUSS_TAIL_BOUND THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC UNIMODAL_TAIL_CONVEX THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `cdf p (X:A->real) (m - y) <= cdf p X (m + y)` MP_TAC THENL
       [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bds" (MP_TAC o SPEC `m - y:real`) THEN
      USE_THEN "bds" (MP_TAC o SPEC `m + y:real`) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:real`; `z:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `cdf p (X:A->real) (m - z) <= cdf p X (m - y) /\
        cdf p X (m + y) <= cdf p X (m + z)`
      MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`b:real`; `n:num`] THEN STRIP_TAC THEN
      EXPAND_TAC "t" THEN MATCH_MP_TAC GRID_TAIL_MOMENT THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e} IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. &0 < y /\ y < e ==> P <= (G:real->real) y`
  (LABEL_TAC "PG") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN BETA_TAC THEN
    SUBGOAL_THEN
     `prob_carrier p DIFF {x | x IN prob_carrier p /\ (X:A->real) x <= m + y}
      IN prob_events p /\
      {x | x IN prob_carrier p /\ X x <= m - y} IN prob_events p`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; RV_CDF_EVENTS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `prob p ((prob_carrier p DIFF
               {x | x IN prob_carrier p /\ (X:A->real) x <= m + y}) UNION
              {x | x IN prob_carrier p /\ X x <= m - y})` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC PROB_MONO THEN
      ASM_SIMP_TAC[PROB_UNION_IN_EVENTS] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_DIFF] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL
       [`p:A prob_space`;
        `prob_carrier p DIFF {x | x IN prob_carrier p /\
           (X:A->real) x <= m + y}`;
        `{x | x IN prob_carrier p /\ (X:A->real) x <= m - y}`]
       PROB_SUBADDITIVE) THEN
      ASM_SIMP_TAC[PROB_COMPL; RV_CDF_EVENTS; GSYM cdf]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ &0 <= P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC EXPECTATION_POS THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      EXPAND_TAC "P" THEN MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. &0 < y ==> (G:real->real) y <= &1` (LABEL_TAC "G1") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN BETA_TAC THEN
    SUBGOAL_THEN `cdf p (X:A->real) (m - y) <= cdf p X (m + y)` MP_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "bds" (MP_TAC o SPEC `m - y:real`) THEN
    USE_THEN "bds" (MP_TAC o SPEC `m + y:real`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `P = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &9 * P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
                                                 ALL_TAC] THEN
    SUBGOAL_THEN `e pow 2 <= (&4 * t) / (&9 * P)` MP_TAC THENL
     [MATCH_MP_TAC SQ_LE_FROM_BELOW THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `&9 * y pow 2 * P <= &9 * y pow 2 * (G:real->real) y`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
                                                       ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        USE_THEN "PG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "core" (fun th ->
        MP_TAC(CONJUNCT1(MP (SPEC `y:real` th) (ASSUME `&0 < y`)))) THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SQ_LE_FROM_BELOW THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `P <= (G:real->real) y /\ G y <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "PG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "G1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * y pow 2 <= &4 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * e pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> &3 * a <= &3 * b:real`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 * t * (&1 - (G:real->real) y) pow 2` THEN CONJ_TAC THENL
   [USE_THEN "core" (fun th ->
      MP_TAC(CONJUNCT2(MP (SPEC `y:real` th) (ASSUME `&0 < y`)))) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC;
                                                   ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

let GAUSS_INEQUALITY = prove
 (`!p:A prob_space X m e.
     unimodal_about p X m /\ integrable p (\x. (X x - m) pow 2) /\ &0 < e
     ==> prob p {x | x IN prob_carrier p /\ abs(X x - m) >= e}
         <= &4 * expectation p (\x. (X x - m) pow 2) / (&9 * e pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `m:real`; `e:real`]
    GAUSS_TAIL_PROB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < &9 * e pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
   REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&4 * x / y = (&4 * x) / y`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SPEC_TAC(`prob p {x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e}`,
           `P:real`) THEN
  REAL_ARITH_TAC);;

let GAUSS_INEQUALITY_ALT = prove
 (`!p:A prob_space X m e.
     unimodal_about p X m /\ integrable p (\x. (X x - m) pow 2) /\
     e <= &2 * sqrt(expectation p (\x. (X x - m) pow 2)) / sqrt(&3)
     ==> prob p {x | x IN prob_carrier p /\ abs(X x - m) >= e}
         <= &1 - e / (sqrt(&3) * sqrt(expectation p (\x. (X x - m) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [unimodal_about]) THEN
  SUBGOAL_THEN `&0
    <= expectation p (\x. ((X:A->real) x - m) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e} IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:A prob_space`; `X:A->real`; `m:real`; `e:real`]
    GAUSS_TAIL_PROB) THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `{x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e}`] PROB_LE_1) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `e <= &2 * sqrt(expectation p (\x. ((X:A->real) x - m) pow 2)) /
         sqrt(&3)` THEN
  SPEC_TAC(`prob p {x | x IN prob_carrier p /\ abs((X:A->real) x - m) >= e}`,
           `P:real`) THEN
  SPEC_TAC(`expectation p (\x. ((X:A->real) x - m) pow 2)`, `t:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `e <= &0` THENL
   [MATCH_MP_TAC(REAL_ARITH `P <= &1 /\ x <= &0 ==> P <= &1 - x`) THEN
    ASM_REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --e * y ==> e * y <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3) * e <= &2 * sqrt t` ASSUME_TAC THENL
   [UNDISCH_TAC `e <= &2 * sqrt t / sqrt(&3)` THEN
    REWRITE_TAC[REAL_ARITH `&2 * x / y = (&2 * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * e pow 2 <= &4 * t` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `sqrt(&3) * e`; `&2 * sqrt t`] REAL_POW_LE2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (e:real) pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&3) * sqrt t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `e <= sqrt(&3) * sqrt t * (&1 - P)` MP_TAC THENL
   [MP_TAC(SPECL [`(e:real) pow 2`; `&3 * (t:real) * (&1 - (P:real)) pow 2`]
      SQRT_MONO_LE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; SQRT_MUL;
                 REAL_ARITH `(P:real) <= &1 ==> &0 <= &1 - P`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 - P ==> (P:real) <= &1 - x`) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Doob's maximal inequality: Pr[max_{k<=n} X_k >= e] <= E[max(X_n,0)] / e   *)
(* for a submartingale and e > 0, and Pr[max_{k<=n} |X_k| >= e] <= E|X_n| /  *)
(* e for a martingale (|X| is then a submartingale).                         *)
(* ------------------------------------------------------------------------- *)

let SUBMARTINGALE_ADD = prove
 (`!p:A prob_space FF X Y.
     submartingale p FF X /\ submartingale p FF Y
     ==> submartingale p FF (\n x. X n x + Y n x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[submartingale; adapted] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. sub_sigma_algebra p ((FF:num->(A->bool)->bool) n)`
  (LABEL_TAC "sub") THENL [ASM_MESON_TAC[filtration]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_ADD THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX];
    MAP_EVERY X_GEN_TAC [`n:num`; `a:A->bool`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A->bool) IN prob_events p` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[sub_sigma_algebra] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `\x. (X:num->A->real) n x * indicator_fn a x`;
                   `\x. (Y:num->A->real) n x * indicator_fn a x`]
      EXPECTATION_ADD) THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `\x. (X:num->A->real) (SUC n) x * indicator_fn a x`;
                   `\x. (Y:num->A->real) (SUC n) x * indicator_fn a x`]
      EXPECTATION_ADD) THEN
    SUBGOAL_THEN
     `!k. integrable p (\x. (X:num->A->real) k x * indicator_fn a x) /\
          integrable p (\x. (Y:num->A->real) k x * indicator_fn a x)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[]]);;

let RUNNING_MAX_GE_EXISTS = prove
 (`!X:num->A->real n x c.
     running_max X n x >= c <=> ?k. k <= n /\ X k x >= c`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[running_max; REAL_MAX_GE;
                                               LE] THEN
  REPEAT GEN_TAC THENL [MESON_TAC[]; MESON_TAC[]]);;

let DOOB_INEQUALITY_GEN = prove
 (`!p:A prob_space FF X n e.
     submartingale p FF X /\ &0 < e
     ==> prob p {x | x IN prob_carrier p /\ ?k. k <= n /\ X k x >= e}
         <= expectation p (\x. max (X n x) (&0)) / e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `\n x. pos_part((X:num->A->real) n x)`; `e:real`; `n:num`]
    NONNEG_SUBMARTINGALE_MAXIMAL) THEN
  ASM_SIMP_TAC[SUBMARTINGALE_POS_PART; pos_part; REAL_LE_MAX;
               REAL_LE_REFL] THEN
  REWRITE_TAC[RUNNING_MAX_GE_EXISTS; real_ge; REAL_MAX_LE; REAL_LE_MAX] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> (e <= &0 <=> F)`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MESON_TAC[REAL_MUL_SYM]);;

let MARTINGALE_ABS_SUBMARTINGALE = prove
 (`!p:A prob_space FF X.
     martingale p FF X ==> submartingale p FF (\n x. abs(X n x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\n x. abs((X:num->A->real) n x)) =
    (\n x. pos_part(X n x) + pos_part(--X n x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; pos_part] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `\n x. pos_part((X:num->A->real) n x)`;
                 `\n x. pos_part(--(X:num->A->real) n x)`]
    SUBMARTINGALE_ADD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBMARTINGALE_POS_PART THEN
    ASM_SIMP_TAC[MARTINGALE_IMP_SUBMARTINGALE];
    MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                   `\n x. --(X:num->A->real) n x`] SUBMARTINGALE_POS_PART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SUPERMARTINGALE_NEG_SUBMARTINGALE THEN
    ASM_SIMP_TAC[MARTINGALE_IMP_SUPERMARTINGALE]]);;

let DOOB_INEQUALITY = prove
 (`!p:A prob_space FF X n e.
     martingale p FF X /\ &0 < e
     ==> prob p {x | x IN prob_carrier p /\ ?k. k <= n /\ abs(X k x) >= e}
         <= expectation p (\x. abs(X n x)) / e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `\n x. abs((X:num->A->real) n x)`; `n:num`; `e:real`]
    DOOB_INEQUALITY_GEN) THEN
  ASM_SIMP_TAC[MARTINGALE_ABS_SUBMARTINGALE] THEN
  REWRITE_TAC[REAL_ARITH `max (abs x) (&0) = abs x`]);;

(* ------------------------------------------------------------------------- *)
(* Kolmogorov's maximal inequality for independent square-integrable X_i:    *)
(* Pr[max_{1<=k<=n} |S_k - E S_k| >= e] <= sum Var X_i / e^2, and the        *)
(* sheet's mean-zero form with Var S_n = sum Var X_i.                        *)
(* ------------------------------------------------------------------------- *)

let SQUARE_INTEGRABLE_SUM_FINITE = prove
 (`!p:A prob_space (X:K->A->real) s.
     FINITE s /\
     (!i. i IN s ==> random_variable p (X i) /\ integrable p (\x. X i x pow 2))
     ==> random_variable p (\x. sum s (\i. X i x)) /\
         integrable p (\x. sum s (\i. X i x) pow 2)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REPEAT DISCH_TAC THEN MP_TAC th)
                             ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (\x. (X:K->A->real) a x + sum t (\i. X i x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(u + v) pow 2
    = u pow 2 + &2 * (u * v) + v pow 2`] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let FIRST_PASSAGE_IN_SIGMA = prove
 (`!p:A prob_space G (S:num->A->real) k t.
     sub_sigma_algebra p G /\ (!j. j <= k ==> measurable_wrt p G (S j))
     ==> {y | y IN prob_carrier p /\ (!j. j < k ==> abs(S j y) < t) /\
              abs(S k y) >= t} IN G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j <= k ==> measurable_wrt p G (\y. abs((S:num->A->real) j y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                   `(S:num->A->real) j`; `abs`]
      MEASURABLE_WRT_COMP_CONTINUOUS) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `abs real_continuous_on (:real)` (fun th ->
      REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`\x:real. x`; `(:real)`] REAL_CONTINUOUS_ON_ABS) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m <= k
        ==> {y | y IN prob_carrier p /\
                 !j. j < m ==> abs((S:num->A->real) j y) < t} IN G`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN
      REWRITE_TAC[LT; SET_RULE `{y | y IN (s:A->bool)} = s`] THEN
      UNDISCH_TAC `sub_sigma_algebra p (G:(A->bool)->bool)` THEN
      REWRITE_TAC[sub_sigma_algebra; sigma_algebra] THEN MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN
       `{y | y IN prob_carrier p /\
             !j. j < SUC m ==> abs((S:num->A->real) j y) < t} =
        {y | y IN prob_carrier p /\ !j. j < m ==> abs(S j y) < t} INTER
        {y | y IN prob_carrier p /\ abs(S m y) < t}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; LT] THEN MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN
      EXISTS_TAC `p:A prob_space` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                       `\y. abs((S:num->A->real) m y)`; `t:real`]
          MEASURABLE_WRT_LT) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN prob_carrier p /\ (!j. j < k
      ==> abs((S:num->A->real) j y) < t) /\
         abs(S k y) >= t} =
    {y | y IN prob_carrier p /\ !j. j < k ==> abs(S j y) < t} INTER
    {y | y IN prob_carrier p /\ abs(S k y) >= t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUB_SIGMA_ALGEBRA_INTER THEN EXISTS_TAC `p:A prob_space` THEN
  ASM_SIMP_TAC[LE_REFL] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                 `\y. abs((S:num->A->real) k y)`; `t:real`]
    MEASURABLE_WRT_GE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[LE_REFL]);;

let KOLMOGOROV_CROSS_TERM_FAMILY = prove
 (`!p:A prob_space (Y:num->A->real) a m k t.
     indep_rv_family p (a..a+m) Y /\
     (!i. a <= i /\ i <= a + m
          ==> integrable p (\x. Y i x pow 2) /\ expectation p (Y i) = &0) /\
     k < m
     ==> expectation p
           (\x. sum(a..a + k) (\i. Y i x) * sum(a + k + 1..a + m) (\i. Y i x) *
                indicator_fn
                  {y | y IN prob_carrier p /\
                       (!j. j < k ==> abs(sum(a..a + j) (\i. Y i y)) < t) /\
                       abs(sum(a..a + k) (\i. Y i y)) >= t} x) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN a..a+m ==> random_variable p ((Y:num->A->real) i)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN a..a+m ==> integrable p ((Y:num->A->real) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(Y:num->A->real) i`; `\x:A. &1`]
      INTEGRABLE_MUL_SQUARE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; REAL_MUL_RID; ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  ABBREV_TAC
   `G1 = sigma_generated (prob_carrier p)
           {{x | x IN prob_carrier p /\ (Y:num->A->real) i x <= v} |
            i IN a..a+k /\ v IN (:real)}` THEN
  ABBREV_TAC
   `G2 = sigma_generated (prob_carrier p)
           {{x | x IN prob_carrier p /\ (Y:num->A->real) i x <= v} |
            i IN a+k+1..a+m /\ v IN (:real)}` THEN
  SUBGOAL_THEN
   `sub_sigma_algebra p (G1:(A->bool)->bool) /\
    sub_sigma_algebra p (G2:(A->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN EXPAND_TAC "G2" THEN CONJ_TAC THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= k
        ==> measurable_wrt p G1 (\y. sum(a..a+j) (\i. (Y:num->A->real) i y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_SUM_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    EXPAND_TAC "G1" THEN MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `A = {y | y IN prob_carrier p /\
             (!j. j < k
                  ==> abs(sum(a..a + j) (\i. (Y:num->A->real) i y)) < t) /\
             abs(sum(a..a + k) (\i. Y i y)) >= t}` THEN
  SUBGOAL_THEN `(A:A->bool) IN G1` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    MP_TAC(ISPECL [`p:A prob_space`; `G1:(A->bool)->bool`;
                   `\j y. sum(a..a+j) (\i. (Y:num->A->real) i y)`;
                   `k:num`; `t:real`] FIRST_PASSAGE_IN_SIGMA) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [UNDISCH_TAC `sub_sigma_algebra p (G1:(A->bool)->bool)` THEN
    REWRITE_TAC[sub_sigma_algebra] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable_wrt p G2 (\y. sum(a+k+1..a+m) (\i. (Y:num->A->real) i y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_SUM_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "G2" THEN
    MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(u:real) * v * w = (u * w) * v`] THEN
  SUBGOAL_THEN
   `!s. s SUBSET a..a+m
        ==> random_variable p (\x. sum s (\i. (Y:num->A->real) i x)) /\
            integrable p (\x. sum s (\i. Y i x) pow 2) /\
            integrable p (\x. sum s (\i. Y i x)) /\
            expectation p (\x. sum s (\i. Y i x)) =
            sum s (\i. expectation p (Y i))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (s:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `s:num->bool`]
      SQUARE_INTEGRABLE_SUM_FINITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(i:num) IN a..a+m` MP_TAC THENL [ASM SET_TAC[];
                                                     ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_SIMP_TAC[];
      SIMP_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!i. i IN s ==> integrable p ((Y:num->A->real) i)` ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUM_FINITE; EXPECTATION_SUM_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `a..a+k SUBSET a..a+m /\ a+k+1..a+m SUBSET a..a+m`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP th (ASSUME `a..a+k SUBSET a..a+m`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `a+k+1..a+m SUBSET a..a+m`))) THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (a+k+1..a+m) (\i. expectation p ((Y:num->A->real) i)) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
         is_conj(snd(dest_imp(snd(dest_forall(concl th)))))
      then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
    `\x. sum(a..a+k) (\i. (Y:num->A->real) i x) * indicator_fn A x`;
    `\x. sum(a+k+1..a+m) (\i. (Y:num->A->real) i x)`]
    EXPECTATION_PRODUCT_INDEP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\x. (sum (a..a + k) (\i. (Y:num->A->real) i x) * indicator_fn A x) *
             sum (a + k + 1..a + m) (\i. Y i x)) =
        (\x. (sum (a..a + k) (\i. Y i x) *
              sum (a + k + 1..a + m) (\i. Y i x)) * indicator_fn A x)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
                        ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_MUL_INDICATOR_FN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(INST_TYPE [`:num`,`:K`]
                     INDEP_RV_FAMILY_BLOCKS_INDEP_RV) THEN
      MAP_EVERY EXISTS_TAC [`Y:num->A->real`; `a..a+k`; `a+k+1..a+m`] THEN
      SUBGOAL_THEN `(a..a+k) UNION (a+k+1..a+m) = a..a+m` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG;
                    NOT_IN_EMPTY] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MUL THEN ASM_SIMP_TAC[LE_REFL; ETA_AX] THEN
      MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

let KOLMOGOROV_INEQUALITY_MEAN_ZERO = prove
 (`!p:A prob_space Y n e.
     indep_rv_family p (1..n) Y /\
     (!i. i IN 1..n
          ==> integrable p (\x. Y i x pow 2) /\ expectation p (Y i) = &0) /\
     &0 < e
     ==> prob p {x | x IN prob_carrier p /\
                     ?k. k IN 1..n /\ abs(sum (1..k) (\i. Y i x)) >= e}
         <= sum (1..n) (\i. variance p (Y i)) / e pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[IN_NUMSEG; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= k /\ k <= 0)`; real_div;
                REAL_MUL_LZERO] THEN
    REWRITE_TAC[SET_RULE `{x | x IN (s:A->bool) /\ F} = {}`; EMPTY_GSPEC;
                PROB_EMPTY;
                REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN 1..n ==> random_variable p ((Y:num->A->real) i)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN 1..n ==> integrable p ((Y:num->A->real) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(Y:num->A->real) i`; `\x:A. &1`]
      INTEGRABLE_MUL_SQUARE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; REAL_MUL_RID; ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `1`; `n - 1`; `e:real`]
    KOLMOGOROV_MAXIMAL_INEQ_SHIFTED) THEN
  SUBGOAL_THEN `1 + (n - 1) = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM IN_NUMSEG] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `i IN 1..n /\ j IN 1..n` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
      MATCH_MP_TAC COVARIANCE_INDEP THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_SIMP_TAC[ETA_AX];
        MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `i:num`; `j:num`]
          INDEP_RV_FAMILY_PAIR) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC INDEP_RV_FAMILY_SUBSET THEN
        EXISTS_TAC `1..n` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`p:A prob_space`; `Y:num->A->real`; `1`; `n - 1`;
                     `k:num`; `e:real`] KOLMOGOROV_CROSS_TERM_FAMILY) THEN
      SUBGOAL_THEN `1 + (n - 1) = n` SUBST1_TAC THENL [ASM_ARITH_TAC;
                                                       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        is_conj(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c:real`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `x:A` THEN AP_TERM_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `1 + k` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EXISTS_TAC `k - 1` THEN
    SUBGOAL_THEN `1 + (k - 1) = k` SUBST1_TAC THENL [ASM_ARITH_TAC;
                                                     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let KOLMOGOROV_INEQUALITY_GEN = prove
 (`!p:A prob_space X n e.
     indep_rv_family p (1..n) X /\
     (!i. i IN 1..n ==> integrable p (\x. X i x pow 2)) /\ &0 < e
     ==> prob p {x | x IN prob_carrier p /\
                     ?k. k IN 1..n /\
                         abs(sum (1..k) (\i. X i x - expectation p (X i)))
                           >= e}
         <= sum (1..n) (\i. variance p (X i)) / e pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN 1..n ==> random_variable p ((X:num->A->real) i) /\
   integrable p (X i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `random_variable p ((X:num->A->real) i)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
       GEN_REWRITE_RULE I [indep_rv_family]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`; `\x:A. &1`]
      INTEGRABLE_MUL_SQUARE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; REAL_MUL_RID; ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                 `\i x. (X:num->A->real) i x - expectation p (X i)`;
                 `n:num`; `e:real`] KOLMOGOROV_INEQUALITY_MEAN_ZERO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN
     EXISTS_TAC `X:num->A->real` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`;
                     `\v. v - expectation p ((X:num->A->real) i)`]
        MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
                   REAL_CONTINUOUS_ON_CONST];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `random_variable p ((X:num->A->real) i) /\ integrable p (X i) /\
        integrable p (\x. X i x pow 2)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH
          `((u:real) - c) pow 2 = u pow 2 + --(&2 * c) * u + c pow 2`] THEN
        MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[INTEGRABLE_CONST] THEN
        MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
        REWRITE_TAC[real_sub] THEN
        MP_TAC(ISPECL [`p:A prob_space`; `(X:num->A->real) i`;
                       `\x:A. --expectation p ((X:num->A->real) i)`]
          EXPECTATION_ADD) THEN
        ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; ETA_AX] THEN
        DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..n)
        (\i. variance p (\x. (X:num->A->real) i x - expectation p (X i))) =
    sum (1..n) (\i. variance p (X i))`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[real_sub] THEN MATCH_MP_TAC VARIANCE_SHIFT THEN
  ASM_SIMP_TAC[ETA_AX]);;

let KOLMOGOROV_INEQUALITY = prove
 (`!p:A prob_space X n e.
     indep_rv_family p (1..n) X /\
     (!i. i IN 1..n ==> integrable p (\x. X i x pow 2) /\
                        expectation p (X i) = &0) /\ &0 < e
     ==> prob p {x | x IN prob_carrier p /\
                     ?k. k IN 1..n /\ abs(sum (1..k) (\i. X i x)) >= e}
         <= variance p (\x. sum (1..n) (\i. X i x)) / e pow 2 /\
         variance p (\x. sum (1..n) (\i. X i x)) =
         sum (1..n) (\i. variance p (X i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `variance p (\x. sum (1..n) (\i. (X:num->A->real) i x)) =
    sum (1..n) (\i. variance p (X i))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VARIANCE_SUM_INDEP_FAMILY THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; INDEP_RV_FAMILY_IMP_KWISE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC KOLMOGOROV_INEQUALITY_MEAN_ZERO THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Etemadi's inequality for independent X_i, n >= 1 and any real a:          *)
(* Pr[max_{1<=k<=n} |S_k| >= 3a] <= 3 max_{1<=k<=n} Pr[|S_k| >= a].          *)
(* ------------------------------------------------------------------------- *)

let ETEMADI_INEQUALITY = prove
 (`!p:A prob_space X n a.
     indep_rv_family p (1..n) X /\ 1 <= n
     ==> prob p {x | x IN prob_carrier p /\
                     ?k. k IN 1..n /\ abs(sum (1..k) (\i. X i x)) >= &3 * a}
         <= &3 * sup {prob p {x | x IN prob_carrier p /\
                                  abs(sum (1..k) (\i. X i x)) >= a} |
                      k IN 1..n}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN 1..n ==> random_variable p ((X:num->A->real) i)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s c. s SUBSET 1..n
          ==> {x | x IN prob_carrier p /\
                   abs(sum s (\i. (X:num->A->real) i x)) >= c}
                     IN prob_events p`
  (LABEL_TAC "ev") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `M = sup {prob p {x | x IN prob_carrier p /\
                         abs(sum (1..k) (\i. (X:num->A->real) i x)) >= a} |
             k IN 1..n}` THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> prob p {x | x IN prob_carrier p /\
                        abs(sum (1..k) (\i. (X:num->A->real) i x)) >= a} <= M`
  (LABEL_TAC "M") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN
    MP_TAC(ISPEC
     `{prob p {x | x IN prob_carrier p /\
                   abs(sum (1..k) (\i. (X:num->A->real) i x)) >= a} |
       k IN 1..n}` SUP_FINITE) THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY] THEN
      ASM_ARITH_TAC;
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = \k. {x | x IN prob_carrier p /\
                 (!j. j < k ==> abs(sum(1..j+1) (\i. (X:num->A->real) i x)) <
                                &3 * a) /\
                 abs(sum(1..k+1) (\i. X i x)) >= &3 * a}` THEN
  ABBREV_TAC
   `B = \k. {x | x IN prob_carrier p /\
                 abs(sum(k+2..n) (\i. (X:num->A->real) i x)) >= &2 * a}` THEN
  SUBGOAL_THEN
   `!k. k <= n - 1
        ==> (A:num->A->bool) k IN prob_events p /\
            (B:num->A->bool) k IN prob_events p /\
            prob p (A k INTER B k) = prob p (A k) * prob p (B k)`
  (LABEL_TAC "AB") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ABBREV_TAC
     `G1 = sigma_generated (prob_carrier p)
             {{x | x IN prob_carrier p /\ (X:num->A->real) i x <= v} |
              i IN 1..k+1 /\ v IN (:real)}` THEN
    ABBREV_TAC
     `G2 = sigma_generated (prob_carrier p)
             {{x | x IN prob_carrier p /\ (X:num->A->real) i x <= v} |
              i IN k+2..n /\ v IN (:real)}` THEN
    SUBGOAL_THEN
     `sub_sigma_algebra p (G1:(A->bool)->bool) /\
      sub_sigma_algebra p (G2:(A->bool)->bool)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G1" THEN EXPAND_TAC "G2" THEN CONJ_TAC THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(A:num->A->bool) k IN G1 /\ (B:num->A->bool) k IN G2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "A" THEN
        MP_TAC(ISPECL [`p:A prob_space`; `G1:(A->bool)->bool`;
                       `\j y. sum(1..j+1) (\i. (X:num->A->real) i y)`;
                       `k:num`; `&3 * a`] FIRST_PASSAGE_IN_SIGMA) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC MEASURABLE_WRT_SUM_FINITE THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN
        REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
        EXPAND_TAC "G1" THEN MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        EXPAND_TAC "B" THEN
        MP_TAC(ISPECL [`p:A prob_space`; `G2:(A->bool)->bool`;
                       `\y. abs(sum(k+2..n) (\i. (X:num->A->real) i y))`;
                       `&2 * a`] MEASURABLE_WRT_GE) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`p:A prob_space`; `G2:(A->bool)->bool`;
                       `\y. sum(k+2..n) (\i. (X:num->A->real) i y)`; `abs`]
          MEASURABLE_WRT_COMP_CONTINUOUS) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_WRT_SUM_FINITE THEN
          ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "G2" THEN
          MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`\x:real. x`; `(:real)`] REAL_CONTINUOUS_ON_ABS) THEN
          REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX]]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `sub_sigma_algebra p (G1:(A->bool)->bool)` THEN
      REWRITE_TAC[sub_sigma_algebra] THEN ASM SET_TAC[];
      UNDISCH_TAC `sub_sigma_algebra p (G2:(A->bool)->bool)` THEN
      REWRITE_TAC[sub_sigma_algebra] THEN ASM SET_TAC[];
      MATCH_MP_TAC(INST_TYPE [`:num`,`:K`] INDEP_RV_FAMILY_BLOCKS) THEN
      MAP_EVERY EXISTS_TAC [`X:num->A->real`; `1..k+1`; `k+2..n`] THEN
      SUBGOAL_THEN `(1..k+1) UNION (k+2..n) = 1..n` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_NUMSEG; NOT_IN_EMPTY] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k <= n - 1 ==> prob p ((B:num->A->bool) k) <= &2 * M`
  (LABEL_TAC "PB") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `prob p ({x | x IN prob_carrier p /\
                   abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a} UNION
              {x | x IN prob_carrier p /\
                   abs(sum (1..k+1) (\i. X i x)) >= a})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN USE_THEN "AB" (fun th ->
       ASM_SIMP_TAC[th]) THEN
      SUBGOAL_THEN `1..k+1 SUBSET 1..n` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ev" (fun th ->
        ASM_SIMP_TAC[PROB_UNION_IN_EVENTS; th; SUBSET_REFL]) THEN
      EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:A` THEN
      SUBGOAL_THEN
       `sum (1..n) (\i. (X:num->A->real) i x) =
        sum (1..k+1) (\i. X i x) + sum (k+2..n) (\i. X i x)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN
        REWRITE_TAC[ARITH_RULE `k + 2 = (k + 1) + 1`] THEN
        MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `prob p {x | x IN prob_carrier p /\
                    abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a} +
        prob p {x | x IN prob_carrier p /\
           abs(sum (1..k+1) (\i. X i x)) >= a}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PROB_SUBADDITIVE THEN CONJ_TAC THEN
        USE_THEN "ev" MATCH_MP_TAC THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= m /\ y <= m ==> x + y <= &2 * m`) THEN
        CONJ_TAC THEN USE_THEN "M" MATCH_MP_TAC THEN
        REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j k. j < k ==> DISJOINT ((A:num->A->bool) j) (A k)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN DISCH_TAC THEN
    EXPAND_TAC "A" THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && free_in `k:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum (0..n-1) (\k. prob p ((A:num->A->bool) k)) <= &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`; `0..n-1`]
      PROB_FINITE_ADDITIVE_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN CONJ_TAC THENL
       [USE_THEN "AB" (fun th -> SIMP_TAC[th]);
        MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN
        MP_TAC(MP (ARITH_RULE `~(j:num = k) ==> j < k \/ k < j`)
                  (ASSUME `~(j:num = k)`)) THEN
        STRIP_TAC THENL
         [ASM_SIMP_TAC[]; ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_SIMP_TAC[]]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC PROB_LE_1 THEN
      MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_NUMSEG;
               LE_0] THEN
      USE_THEN "AB" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\
         ?k. k IN 1..n /\ abs(sum (1..k) (\i. (X:num->A->real) i x)) >= &3 * a}
    SUBSET
    {x | x IN prob_carrier p /\ abs(sum (1..n) (\i. X i x)) >= a} UNION
    UNIONS (IMAGE (\k. (A:num->A->bool) k INTER B k) (0..n-1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; UNIONS_IMAGE; IN_NUMSEG; LE_0;
                IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `\k. 1 <= k /\ k <= n /\
                      abs(sum (1..k) (\i. (X:num->A->real) i x)) >= &3 * a`
      num_WOP) THEN
    REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [EXISTS_TAC `k:num` THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k0 - 1` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "A" THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `1 <= k0 ==> k0 - 1 + 1 = k0 /\ k0 - 1 + 2 = k0 + 1`] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j + 1` o check (fun th ->
        is_forall(concl th) && free_in `k0:num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[DE_MORGAN_THM; real_ge; REAL_NOT_LE] THEN
      STRIP_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN ASM_ARITH_TAC;
      SUBGOAL_THEN
       `sum (1..n) (\i. (X:num->A->real) i x) =
        sum (1..k0) (\i. X i x) + sum (k0+1..n) (\i. X i x)`
      MP_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~(abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a)` THEN
      UNDISCH_TAC `abs(sum (1..k0) (\i. (X:num->A->real) i x)) >= &3 * a` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p {x | x IN prob_carrier p /\
                            abs(sum (1..n) (\i. (X:num->A->real) i x))
                              >= a}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PROB_POSITIVE THEN USE_THEN "ev" MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET_REFL];
      USE_THEN "M" MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (\k. (A:num->A->bool) k INTER B k) (0..n-1))
     IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_NUMSEG;
             LE_0] THEN
    USE_THEN "AB" (fun th -> SIMP_TAC[th; PROB_INTER_IN_EVENTS]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\
         ?k. k IN 1..n /\ abs(sum (1..k) (\i. (X:num->A->real) i x)) >= &3 * a}
    IN prob_events p`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN prob_carrier p /\
           ?k. k IN 1..n /\
               abs(sum (1..k) (\i. (X:num->A->real) i x)) >= &3 * a} =
      UNIONS (IMAGE (\k. {x | x IN prob_carrier p /\
                              abs(sum (1..k) (\i. X i x)) >= &3 * a}) (1..n))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ev" MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `prob p ({x | x IN prob_carrier p /\
                 abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a} UNION
            UNIONS (IMAGE (\k. (A:num->A->bool) k INTER B k) (0..n-1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ev" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `prob p {x | x IN prob_carrier p /\
                abs(sum (1..n) (\i. (X:num->A->real) i x)) >= a} +
    prob p (UNIONS (IMAGE (\k. (A:num->A->bool) k INTER B k) (0..n-1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_SUBADDITIVE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ev" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= m /\ y <= &2 * m ==> x + y <= &3 * m`) THEN
  CONJ_TAC THENL
   [USE_THEN "M" MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..n-1) (\k. prob p ((A:num->A->bool) k INTER B k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_SUBADDITIVE THEN
    USE_THEN "AB" (fun th -> SIMP_TAC[th; PROB_INTER_IN_EVENTS]);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..n-1) (\k. prob p ((A:num->A->bool) k) * (&2 * M))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN USE_THEN "AB" (fun th -> ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN USE_THEN "PB" (fun th ->
      ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC PROB_POSITIVE THEN USE_THEN "AB" (fun th -> ASM_SIMP_TAC[th]);
    REWRITE_TAC[SUM_RMUL] THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= m /\ s <= &1 /\ s * m <= &1 * m ==> s * (&2 * m) <= &2 * m`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Events mutually independent of a family: the complement form Pr[a /\ B_j  *)
(* (j in U) /\ ~B_j (j in S)] = Pr[a] Pr[B_j (j in U) /\ ~B_j (j in S)].     *)
(* ------------------------------------------------------------------------- *)

let CYL_IN_EVENTS = prove
 (`!p:A prob_space (B:K->A->bool) U S.
     FINITE U /\ FINITE S /\
     (!j. j IN U ==> B j IN prob_events p) /\
     (!j. j IN S ==> B j IN prob_events p)
     ==> {y | y IN prob_carrier p /\ (!j. j IN U ==> y IN B j) /\
              (!j. j IN S ==> ~(y IN B j))} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{y | y IN prob_carrier p /\ (!j. j IN U ==> y IN (B:K->A->bool) j) /\
         (!j. j IN S ==> ~(y IN B j))} =
    INTERS ((prob_carrier p) INSERT
            (IMAGE B U UNION IMAGE (\j. prob_carrier p DIFF B j) S))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTERS; FORALL_IN_INSERT; FORALL_IN_UNION;
                FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
  ASM_SIMP_TAC[NOT_INSERT_EMPTY; COUNTABLE_INSERT; COUNTABLE_UNION;
               COUNTABLE_IMAGE; FINITE_IMP_COUNTABLE] THEN
  REWRITE_TAC[INSERT_SUBSET; UNION_SUBSET; SUBSET; FORALL_IN_IMAGE;
              PROB_CARRIER_IN_EVENTS] THEN
  ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]);;

let EVENT_MUTUALLY_INDEP_CYL = prove
 (`!p:A prob_space a (t:K->bool) B S U.
     event_mutually_indep p a t B /\ FINITE S /\ FINITE U /\
     S SUBSET t /\ U SUBSET t
     ==> prob p (a INTER {y | y IN prob_carrier p /\
                              (!j. j IN U ==> y IN B j) /\
                              (!j. j IN S ==> ~(y IN B j))}) =
         prob p a * prob p {y | y IN prob_carrier p /\
                                (!j. j IN U ==> y IN B j) /\
                                (!j. j IN S ==> ~(y IN B j))}`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [X_GEN_TAC `U:K->bool` THEN REWRITE_TAC[NOT_IN_EMPTY; EMPTY_SUBSET] THEN
    REPEAT DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [event_mutually_indep]) THEN
    ASM_CASES_TAC `U:K->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY; SET_RULE `{y | y IN (s:A->bool)} = s`] THEN
      SUBGOAL_THEN `a INTER prob_carrier p = (a:A->bool)` SUBST1_TAC THENL
       [MP_TAC(ISPECL [`p:A prob_space`; `a:A->bool`] PROB_EVENT_SUBSET) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PROB_SPACE; REAL_MUL_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{y | y IN prob_carrier p /\ (!j. j IN U ==> y IN (B:K->A->bool) j)} =
      INTERS (IMAGE B U)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; INTERS_IMAGE] THEN
     X_GEN_TAC `y:A` THEN
      EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o
        check (fun th -> concl th = `~(U:K->bool = {})`)) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `j:K`) THEN
      MP_TAC(ISPECL [`p:A prob_space`;
                     `(B:K->A->bool) j`] PROB_EVENT_SUBSET) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                      ASM SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:K`; `S:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `U:K->bool` THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [event_mutually_indep]) THEN
  ABBREV_TAC
   `E = \V W. {y | y IN prob_carrier p /\
                   (!j. j IN V ==> y IN (B:K->A->bool) j) /\
                   (!j. j IN W ==> ~(y IN B j))}` THEN
  SUBGOAL_THEN
   `!V W. FINITE V /\ FINITE W /\ V SUBSET t /\ W SUBSET t
          ==> (E:(K->bool)->(K->bool)->A->bool) V W IN prob_events p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN MATCH_MP_TAC CYL_IN_EVENTS THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN prob_carrier p /\ (!j. j IN U ==> y IN (B:K->A->bool) j) /\
         (!j. j IN x INSERT S ==> ~(y IN B j))} =
    E U S DIFF E (x INSERT U) S /\
    {y | y IN prob_carrier p /\ (!j. j IN U ==> y IN (B:K->A->bool) j) /\
         (!j. j IN S ==> ~(y IN B j))} = E U S /\
    {y | y IN prob_carrier p /\ (!j. j IN x INSERT U
       ==> y IN (B:K->A->bool) j) /\
         (!j. j IN S ==> ~(y IN B j))} = E (x INSERT U) S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM;
                                    IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `S SUBSET (t:K->bool) /\
  x INSERT U SUBSET t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "IH" (fun th ->
    MP_TAC(SPEC `U:K->bool` th) THEN MP_TAC(SPEC `(x:K) INSERT U` th)) THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(E:(K->bool)->(K->bool)->A->bool) (x INSERT U) S SUBSET E U S`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(E:(K->bool)->(K->bool)->A->bool) U S IN prob_events p /\
    E (x INSERT U) S IN prob_events p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      free_in `E:(K->bool)->(K->bool)->A->bool` (concl th))) THEN
    ASM_REWRITE_TAC[FINITE_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a INTER (E U S DIFF E (x INSERT U) S) =
    (a INTER (E:(K->bool)->(K->bool)->A->bool) U S) DIFF
    (a INTER E (x INSERT U) S)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_DIFF_SUBSET; PROB_INTER_IN_EVENTS;
               SET_RULE `s SUBSET t
                         ==> a INTER s SUBSET a INTER (t:A->bool)`] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Lovasz local lemma: avoiding events, and the chain bound prod_{j in V} (1 *)
(* - x_j) Pr[avoid U] <= Pr[avoid U u V] from the conditional bounds.        *)
(* ------------------------------------------------------------------------- *)

let AVOID_IN_EVENTS = prove
 (`!p:A prob_space (B:K->A->bool) W.
     FINITE W /\ (!j. j IN W ==> B j IN prob_events p)
     ==> {y | y IN prob_carrier p /\ !j. j IN W ==> ~(y IN B j)}
         IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `B:K->A->bool`; `{}:K->bool`; `W:K->bool`]
    CYL_IN_EVENTS) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY]);;

let LLL_CHAIN = prove
 (`!p:A prob_space (B:K->A->bool) x U V.
     FINITE U /\ FINITE V /\ DISJOINT U V /\
     (!j. j IN U UNION V ==> B j IN prob_events p) /\
     (!j. j IN V ==> x j <= &1) /\
     (!W j. W SUBSET V /\ j IN V /\ ~(j IN W)
            ==> prob p (B j INTER {y | y IN prob_carrier p /\
                                       !k. k IN U UNION W ==> ~(y IN B k)})
                <= x j * prob p {y | y IN prob_carrier p /\
                                     !k. k IN U UNION W ==> ~(y IN B k)})
     ==> product V (\j. &1 - x j) *
         prob p {y | y IN prob_carrier p /\ !k. k IN U ==> ~(y IN B k)}
         <= prob p {y | y IN prob_carrier p /\
                        !k. k IN U UNION V ==> ~(y IN B k)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!W. W SUBSET V
        ==> product W (\j. &1 - x j) *
            prob p {y | y IN prob_carrier p /\ !k. k IN U
               ==> ~(y IN (B:K->A->bool) k)}
            <= prob p {y | y IN prob_carrier p /\
                           !k. k IN U UNION W ==> ~(y IN B k)}`
  (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[SUBSET_REFL]) THEN
  SUBGOAL_THEN `!W. FINITE W ==> W SUBSET V
        ==> product W (\j. &1 - x j) *
            prob p {y | y IN prob_carrier p /\ !k. k IN U
               ==> ~(y IN (B:K->A->bool) k)}
            <= prob p {y | y IN prob_carrier p /\
                           !k. k IN U UNION W ==> ~(y IN B k)}`
  (fun th -> ASM_MESON_TAC[th; FINITE_SUBSET]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; UNION_EMPTY; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:K`; `W:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  ABBREV_TAC `D = {y | y IN prob_carrier p /\
                       !k. k IN U UNION W ==> ~(y IN (B:K->A->bool) k)}` THEN
  SUBGOAL_THEN `(D:A->bool) IN prob_events p /\
  (B:K->A->bool) j IN prob_events p`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC AVOID_IN_EVENTS THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN prob_carrier p /\ !k. k IN U UNION j INSERT W
      ==> ~(y IN (B:K->A->bool) k)} =
    D DIFF (B j INTER D)`
  SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_INTER;
                                    IN_UNION; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_DIFF_SUBSET; PROB_INTER_IN_EVENTS; INTER_SUBSET] THEN
  USE_THEN "IH" (MP_TAC o C MP (ASSUME `W SUBSET (V:K->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `prob p ((B:K->A->bool) j INTER D)
    <= x j * prob p D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - (x:K->real) j` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `j:K` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      not(free_in `B:K->A->bool` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - (x:K->real) j) * prob p (D:A->bool)` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lovasz local lemma, asymmetric form: if each B_i is mutually independent  *)
(* of the B_j outside its neighbourhood N_i and Pr[B_i] <= x_i prod_{j in    *)
(* N_i} (1 - x_j) with 0 <= x_i < 1, then Pr[avoid all B_i] >= prod (1 -     *)
(* x_i) > 0; symmetric form: if each B_i is mutually independent of all but  *)
(* at most d others and e q (d + 1) <= 1 for Pr[B_i] <= q, then Pr[avoid all *)
(* B_i] > 0.                                                                 *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_SUBSET_UNIT_LE = prove
 (`!(f:K->real) s t.
     FINITE t /\ s SUBSET t /\ (!j. j IN t ==> &0 <= f j /\ f j <= &1)
     ==> product t f <= product s f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = (s:K->bool) UNION (t DIFF s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:K->bool) /\
  FINITE (t DIFF s:K->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_UNION; SET_RULE `DISJOINT (s:K->bool) (t DIFF s)`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM SET_TAC[];
    MATCH_MP_TAC PRODUCT_LE_1 THEN ASM SET_TAC[]]);;

let LLL_KEY = prove
 (`!p:A prob_space (B:K->A->bool) s N x.
     FINITE s /\
     (!i. i IN s
          ==> N i SUBSET s /\
              event_mutually_indep p (B i) (s DIFF (i INSERT N i)) B /\
              &0 <= x i /\ x i < &1 /\
              prob p (B i) <= x i * product (N i) (\j. &1 - x j))
     ==> !n W i. CARD W = n /\ W SUBSET s /\ i IN s /\ ~(i IN W)
                 ==> prob p (B i INTER {y | y IN prob_carrier p /\
                                            !k. k IN W ==> ~(y IN B k)})
                     <= x i * prob p {y | y IN prob_carrier p /\
                                          !k. k IN W ==> ~(y IN B k)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")) THEN
  SUBGOAL_THEN `!j. j IN s ==> (B:K->A->bool) j IN prob_events p`
  (LABEL_TAC "Bev") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "H" (fun th ->
      MP_TAC(MP (SPEC `j:K` th) (ASSUME `(j:K) IN s`))) THEN
    SIMP_TAC[event_mutually_indep];
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`W:K->bool`; `i:K`] THEN STRIP_TAC THEN
  USE_THEN "H" (fun th ->
    STRIP_ASSUME_TAC(MP (SPEC `i:K` th) (ASSUME `(i:K) IN s`))) THEN
  SUBGOAL_THEN `FINITE (W:K->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `U = (W:K->bool) DIFF N (i:K)` THEN
  ABBREV_TAC `V = (W:K->bool) INTER N (i:K)` THEN
  SUBGOAL_THEN
   `FINITE (U:K->bool) /\ FINITE (V:K->bool) /\ DISJOINT U V /\
   U UNION V = W /\
    U SUBSET s /\ V SUBSET N (i:K)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "V"] THEN
    ASM_SIMP_TAC[FINITE_DIFF; FINITE_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. FINITE Z /\ Z SUBSET s
        ==> {y | y IN prob_carrier p /\ !k. k IN Z
           ==> ~(y IN (B:K->A->bool) k)}
            IN prob_events p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC AVOID_IN_EVENTS THEN
   ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "Bev" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `prob p ((B:K->A->bool) i INTER
            {y | y IN prob_carrier p /\ !k. k IN U ==> ~(y IN B k)}) =
    prob p (B i) *
    prob p {y | y IN prob_carrier p /\ !k. k IN U ==> ~(y IN B k)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `(B:K->A->bool) i`;
                   `s DIFF ((i:K) INSERT N i)`; `B:K->A->bool`; `U:K->bool`;
                   `{}:K->bool`] EVENT_MUTUALLY_INDEP_CYL) THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL [MAP_EVERY EXPAND_TAC ["U"] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product (V:K->bool) (\j. &1 - x j) *
    prob p {y | y IN prob_carrier p /\ !k. k IN U ==> ~(y IN (B:K->A->bool) k)}
    <= prob p {y | y IN prob_carrier p /\ !k. k IN U UNION V ==> ~(y IN B k)}`
  MP_TAC THENL
   [MATCH_MP_TAC LLL_CHAIN THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "H" (MP_TAC o SPEC `j:K`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`Z:K->bool`; `j:K`] THEN STRIP_TAC THEN
      USE_THEN "IH" (MP_TAC o SPEC `CARD((U:K->bool) UNION Z)`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `CARD(W:K->bool) = n` THEN DISCH_THEN(SUBST1_TAC o
         SYM) THEN
        MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `product (N(i:K)) (\j. &1 - x j) <= product (V:K->bool) (\j. &1 - x j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_SUBSET_UNIT_LE THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET];
      X_GEN_TAC `j:K` THEN DISCH_TAC THEN USE_THEN "H" (MP_TAC o
        SPEC `j:K`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= prob p {y | y IN prob_carrier p /\ !k. k IN U
      ==> ~(y IN (B:K->A->bool) k)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `prob p ((B:K->A->bool) i INTER
                      {y | y IN prob_carrier p /\
                           !k. k IN U ==> ~(y IN B k)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN
    ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN
    UNDISCH_TAC `(U:K->bool) UNION V = W` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(x:K->real) i * product V (\j. &1 - x j) *
              prob p {y | y IN prob_carrier p /\ !k. k IN U
                 ==> ~(y IN (B:K->A->bool) k)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(x:K->real) i * product (N i) (\j. &1 - x j)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let LOVASZ_LOCAL_LEMMA = prove
 (`!p:A prob_space (B:K->A->bool) s N x.
    FINITE s /\
    (!i. i IN s
         ==> N i SUBSET s /\
             event_mutually_indep p (B i) (s DIFF (i INSERT N i)) B /\
             &0 <= x i /\ x i < &1 /\
             prob p (B i) <= x i * product (N i) (\j. &1 - x j))
    ==> product s (\i. &1 - x i)
        <= prob p {y | y IN prob_carrier p /\ !i. i IN s ==> ~(y IN B i)} /\
        &0 < product s (\i. &1 - x i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `B:K->A->bool`; `x:K->real`; `{}:K->bool`;
                   `s:K->bool`] LLL_CHAIN) THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; DISJOINT_EMPTY; UNION_EMPTY; NOT_IN_EMPTY;
                    SET_RULE `{y | y IN (s:A->bool)} = s`; PROB_SPACE;
                    REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN
      ASM_SIMP_TAC[event_mutually_indep];
      X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`W:K->bool`; `j:K`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`p:A prob_space`; `B:K->A->bool`; `s:K->bool`;
                     `N:K->K->bool`; `x:K->real`] LLL_KEY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`CARD(W:K->bool)`; `W:K->bool`; `j:K`]) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let LOVASZ_SYMMETRIC_WEIGHT = prove
 (`!d q. exp(&1) * q * &(d + 1) <= &1
         ==> q <= inv(&d + &2) * ((&d + &1) / (&d + &2)) pow d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + inv(&d + &1)) pow (d + 1) <= exp(&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
   EXISTS_TAC `exp(inv(&d + &1)) pow (d + 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_N; REAL_OF_NUM_ADD] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_ADD; REAL_MUL_RINV;
               REAL_ARITH `~(&d + &1 = &0)`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + inv(&d + &1) = inv((&d + &1) / (&d + &2))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_INV; REAL_POW_ADD; REAL_POW_1]) THEN
  SUBGOAL_THEN `&0 < ((&d + &1) / (&d + &2)) pow d` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `d:num` REAL_POS) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`((&d + &1) / (&d + &2)) pow d`, `w:real`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`&d:real`, `a:real`) THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = w * (a + &1) / (a + &2)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(a + &2) * w = c / (a + &1)` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 <= a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= a ==> &0 < a + &1`] THEN
  SUBGOAL_THEN `&1 <= exp(&1) * c` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `inv(c:real)`; `exp(&1)`] REAL_LE_LMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `q * (a + &1) <= &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(q * (a + &1)) * (exp(&1) * c)` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`exp(&1) * q * (a + &1)`; `&1`; `c:real`] REAL_LE_RMUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

let LOVASZ_LOCAL_LEMMA_SYMMETRIC = prove
 (`!p:A prob_space (B:K->A->bool) s d q.
    FINITE s /\
    (!i. i IN s
         ==> ?t. t SUBSET s DELETE i /\ CARD ((s DELETE i) DIFF t) <= d /\
                 event_mutually_indep p (B i) t B) /\
    (!i. i IN s ==> prob p (B i) <= q) /\
    exp(&1) * q * &(d + 1) <= &1
    ==> &0 < prob p {y | y IN prob_carrier p /\ !i. i IN s ==> ~(y IN B i)}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:K->K->bool` (LABEL_TAC "t"))
    (CONJUNCTS_THEN2 (LABEL_TAC "q") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `B:K->A->bool`; `s:K->bool`;
                 `\i:K. (s DELETE i) DIFF t i`; `\i:K. inv(&d + &2)`]
                LOVASZ_LOCAL_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[REAL_LTE_TRANS]] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REMOVE_THEN "t" (STRIP_ASSUME_TAC o C MP (ASSUME `(i:K) IN s`) o
    SPEC `i:K`) THEN
  REMOVE_THEN "q" (ASSUME_TAC o C MP (ASSUME `(i:K) IN s`) o SPEC `i:K`) THEN
  SUBGOAL_THEN `s DIFF (i INSERT ((s DELETE i) DIFF t i)) = (t:K->K->bool) i`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CONST; FINITE_DIFF; FINITE_DELETE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&d + &2) * ((&d + &1) / (&d + &2)) pow d` THEN
  ASM_SIMP_TAC[LOVASZ_SYMMETRIC_WEIGHT] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - inv(&d + &2) = (&d + &1) / (&d + &2)` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &d + &2`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A random subset R of a ground set u with independent memberships: events  *)
(* determined by R on a finite set of coordinates; independence of events on *)
(* disjoint coordinate sets; Harris's inequality (increasing events are      *)
(* positively correlated, and its complement forms); Janson's inequality for *)
(* increasing events determined by finite coordinate sets a_i, with Delta    *)
(* summed over ordered pairs i ~ j (a_i, a_j meeting), and the sheet's form  *)
(* B_i = {a_i SUBSET R}.                                                     *)
(* ------------------------------------------------------------------------- *)

let RANDOM_SUBSET_DECOMP = prove
 (`!p:A prob_space (R:A->U->bool) y w v K.
     {x | x IN prob_carrier p /\ (!j. j IN y ==> j IN R x) /\
          R x INTER (v INSERT w) IN K} =
     {x | x IN prob_carrier p /\ (!j. j IN v INSERT y ==> j IN R x) /\
          R x INTER w IN {z | v INSERT z IN K}} UNION
     ({x | x IN prob_carrier p /\ (!j. j IN y ==> j IN R x) /\
           R x INTER w IN K} DIFF
      {x | x IN prob_carrier p /\ (!j. j IN v INSERT y ==> j IN R x) /\
           R x INTER w IN K})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_ELIM_THM; FORALL_IN_INSERT] THEN
  X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(v:U) IN R(x:A)` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `R x INTER (v INSERT w) = v INSERT (R (x:A) INTER w):U->bool`
    SUBST1_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    SUBGOAL_THEN `R x INTER (v INSERT w) = R (x:A) INTER w:U->bool`
    SUBST1_TAC THENL [ASM SET_TAC[]; MESON_TAC[]]]);;

let RANDOM_SUBSET_CYL_IN_EVENTS = prove
 (`!p:A prob_space (R:A->U->bool) u.
     (!v. v IN u ==> {x | x IN prob_carrier p /\ v IN R x} IN prob_events p)
     ==> !w y K. FINITE w /\ w SUBSET u /\ FINITE y /\ y SUBSET u
                 ==> {x | x IN prob_carrier p /\ (!j. j IN y ==> j IN R x) /\
                          R x INTER w IN K} IN prob_events p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_EMPTY] THEN
    ASM_CASES_TAC `({}:U->bool) IN K` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; PROB_EMPTY_IN_EVENTS] THEN
    MP_TAC(ISPECL
     [`p:A prob_space`;
      `\v:U. {x | x IN prob_carrier (p:A prob_space) /\
         v IN (R:A->U->bool) x}`;
      `y:U->bool`; `{}:U->bool`] CYL_IN_EVENTS) THEN
    ASM_SIMP_TAC[FINITE_EMPTY; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:U`; `w:U->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  REMOVE_THEN "IH" (ASSUME_TAC o REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] o
                    C MP (ASSUME `(w:U->bool) SUBSET u`)) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RANDOM_SUBSET_DECOMP] THEN
  MATCH_MP_TAC PROB_UNION_IN_EVENTS THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC PROB_DIFF_IN_EVENTS THEN CONJ_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT;
                                                  INSERT_SUBSET]);;

let RANDOM_SUBSET_INTERS_PROB = prove
 (`!p:A prob_space (R:A->U->bool) u y.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
     FINITE y /\ y SUBSET u
     ==> prob p {x | x IN prob_carrier p /\ !j. j IN y ==> j IN R x} =
         product y (\v. prob p {x | x IN prob_carrier p /\ v IN R x})`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:U->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES;
                    SET_RULE `{x | x IN (s:A->bool)} = s`; PROB_SPACE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [indep_event_family]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:U->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; INTERS_IMAGE; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MESON_TAC[]);;

let PROB_UNION_DIFF_SUBSET = prove
 (`!p:A prob_space a b c.
     a IN prob_events p /\ b IN prob_events p /\ c IN prob_events p /\
     c SUBSET b /\ a INTER b SUBSET c
     ==> prob p (a UNION (b DIFF c)) = prob p a + prob p b - prob p c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PROB_UNION; PROB_DIFF_IN_EVENTS; PROB_DIFF_SUBSET] THEN
  SUBGOAL_THEN `a INTER (b DIFF c) = {}:A->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[PROB_EMPTY] THEN REAL_ARITH_TAC]);;

let RANDOM_SUBSET_DECOMP_PROB = prove
 (`!p:A prob_space (R:A->U->bool) u y w v K.
     (!v. v IN u ==> {x | x IN prob_carrier p /\ v IN R x} IN prob_events p) /\
     FINITE w /\ w SUBSET u /\ FINITE y /\ y SUBSET u /\ v IN u
     ==> prob p {x | x IN prob_carrier p /\ (!j. j IN y ==> j IN R x) /\
                     R x INTER (v INSERT w) IN K} =
         prob p {x | x IN prob_carrier p /\
                     (!j. j IN v INSERT y ==> j IN R x) /\
                     R x INTER w IN {z | v INSERT z IN K}} +
         prob p {x | x IN prob_carrier p /\ (!j. j IN y ==> j IN R x) /\
                     R x INTER w IN K} -
         prob p {x | x IN prob_carrier p /\
                     (!j. j IN v INSERT y ==> j IN R x) /\
                     R x INTER w IN K}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RANDOM_SUBSET_DECOMP] THEN
  MATCH_MP_TAC PROB_UNION_DIFF_SUBSET THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`]
    RANDOM_SUBSET_CYL_IN_EVENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FINITE_INSERT; INSERT_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; FORALL_IN_INSERT] THEN
  MESON_TAC[]);;

let RANDOM_SUBSET_CYL_PROB = prove
 (`!p:A prob_space (R:A->U->bool) u.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x})
     ==> !w y K. FINITE w /\ w SUBSET u /\ FINITE y /\ y SUBSET u /\
                 DISJOINT y w
                 ==> prob p {x | x IN prob_carrier p /\
                                 (!j. j IN y ==> j IN R x) /\
                                 R x INTER w IN K} =
                     product y
                       (\v. prob p {x | x IN prob_carrier p /\ v IN R x}) *
                     prob p {x | x IN prob_carrier p /\ R x INTER w IN K}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!v. v IN u
        ==> {x | x IN prob_carrier p /\
           v IN (R:A->U->bool) x} IN prob_events p`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
     GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_EMPTY] THEN
    ASM_CASES_TAC `({}:U->bool) IN K` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; PROB_EMPTY; REAL_MUL_RZERO; PROB_SPACE;
                    SET_RULE `{x | x IN (s:A->bool)} = s`; REAL_MUL_RID] THEN
    MATCH_MP_TAC RANDOM_SUBSET_INTERS_PROB THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:U`; `w:U->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  REMOVE_THEN "IH" (ASSUME_TAC o REWRITE_RULE[IMP_IMP] o
                    C MP (ASSUME `(w:U->bool) SUBSET u`)) THEN
  X_GEN_TAC `y:U->bool` THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `K:(U->bool)->bool` THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ R x INTER (v INSERT w) IN K} =
    {x | x IN prob_carrier p /\ (!j. j IN {} ==> j IN (R:A->U->bool) x) /\
         R x INTER (v INSERT w) IN K} /\
    {x | x IN prob_carrier p /\ R x INTER w IN K} =
    {x | x IN prob_carrier p /\ (!j. j IN {} ==> j IN (R:A->U->bool) x) /\
         R x INTER w IN K}`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`]
    RANDOM_SUBSET_DECOMP_PROB) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FINITE_EMPTY; EMPTY_SUBSET] THEN
  SUBGOAL_THEN `DISJOINT (y:U->bool) w /\ ~(v IN y)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_INSERT; INSERT_SUBSET; FINITE_EMPTY; EMPTY_SUBSET;
               DISJOINT_INSERT; DISJOINT_EMPTY; FINITE_SING; SING_SUBSET] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; PRODUCT_SING] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONV_TAC REAL_RING);;

let RANDOM_SUBSET_EVENT_IN_EVENTS = prove
 (`!p:A prob_space (R:A->U->bool) u w K.
     (!v. v IN u ==> {x | x IN prob_carrier p /\ v IN R x} IN prob_events p) /\
     FINITE w /\ w SUBSET u
     ==> {x | x IN prob_carrier p /\ R x INTER w IN K} IN prob_events p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`]
    RANDOM_SUBSET_CYL_IN_EVENTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:U->bool`; `{}:U->bool`;
                             `K:(U->bool)->bool`]) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY]);;

let RANDOM_SUBSET_STEP_PROB = prove
 (`!p:A prob_space (R:A->U->bool) u w v K.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
     FINITE w /\ w SUBSET u /\ v IN u /\ ~(v IN w)
     ==> prob p {x | x IN prob_carrier p /\ R x INTER (v INSERT w) IN K} =
         prob p {x | x IN prob_carrier p /\ v IN R x} *
         prob p {x | x IN prob_carrier p /\ v INSERT (R x INTER w) IN K} +
         (&1 - prob p {x | x IN prob_carrier p /\ v IN R x}) *
         prob p {x | x IN prob_carrier p /\ R x INTER w IN K}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. v IN u
        ==> {x | x IN prob_carrier p /\
           v IN (R:A->U->bool) x} IN prob_events p`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
     GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `{}:U->bool`;
                 `w:U->bool`; `v:U`; `K:(U->bool)->bool`]
    RANDOM_SUBSET_DECOMP_PROB) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`]
    RANDOM_SUBSET_CYL_PROB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FINITE_SING; SING_SUBSET; DISJOINT_INSERT; DISJOINT_EMPTY;
               PRODUCT_SING] THEN
  REWRITE_TAC[IN_ELIM_THM;
    REAL_ARITH `!a b c:real. a * b + c - a * c = a * b + (&1 - a) * c`]);;

let HARRIS_STEP_ALGEBRA = prove
 (`!a g0 g1 h0 h1 k0 k1:real.
     &0 <= a /\ a <= &1 /\ g0 <= g1 /\ h0 <= h1 /\
     g0 * h0 <= k0 /\ g1 * h1 <= k1
     ==> (a * g1 + (&1 - a) * g0) * (a * h1 + (&1 - a) * h0)
         <= a * k1 + (&1 - a) * k0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a * (&1 - a):real`; `(g1 - g0) * (h1 - h0):real`]
    REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `g1 * h1:real`; `k1:real`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`&1 - a:real`; `g0 * h0:real`; `k0:real`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN REAL_ARITH_TAC);;

let HARRIS_INEQUALITY = prove
 (`!p:A prob_space (R:A->U->bool) u t G H.
    indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
    FINITE t /\ t SUBSET u /\
    (!y z. y IN G /\ y SUBSET z /\ z SUBSET t ==> z IN G) /\
    (!y z. y IN H /\ y SUBSET z /\ z SUBSET t ==> z IN H)
    ==> prob p {x | x IN prob_carrier p /\ R x INTER t IN G} *
        prob p {x | x IN prob_carrier p /\ R x INTER t IN H}
        <= prob p {x | x IN prob_carrier p /\
                       R x INTER t IN G /\ R x INTER t IN H}`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!v. v IN u
        ==> {x | x IN prob_carrier p /\
           v IN (R:A->U->bool) x} IN prob_events p`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
     GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_EMPTY] THEN
    ASM_CASES_TAC `({}:U->bool) IN G` THEN
    ASM_CASES_TAC `({}:U->bool) IN H` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; PROB_EMPTY; PROB_SPACE; REAL_MUL_LZERO;
                    REAL_MUL_RZERO; SET_RULE `{x | x IN (s:A->bool)} = s`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:U`; `t:U->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  REMOVE_THEN "IH" (LABEL_TAC "IH" o
    REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] o
    C MP (ASSUME `(t:U->bool) SUBSET u`)) THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM] THEN
  X_GEN_TAC `G:(U->bool)->bool` THEN X_GEN_TAC `H:(U->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G") (LABEL_TAC "H")) THEN
  REWRITE_TAC[GSYM IN_INTER] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `t:U->bool`;
                 `v:U`] RANDOM_SUBSET_STEP_PROB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC HARRIS_STEP_ALGEBRA THEN
  SUBGOAL_THEN
   `!K. {x | x IN prob_carrier p /\ v INSERT ((R:A->U->bool) x INTER t) IN K} =
        {x | x IN prob_carrier p /\ R x INTER t IN {z | v INSERT z IN K}}`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. {x | x IN prob_carrier p /\ (R:A->U->bool) x INTER t IN K}
        IN prob_events p`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_POSITIVE; PROB_LE_1] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "G" MATCH_MP_TAC THEN EXISTS_TAC `(R:A->U->bool) x INTER t` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "H" MATCH_MP_TAC THEN EXISTS_TAC `(R:A->U->bool) x INTER t` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_INTER] THEN USE_THEN "IH" MATCH_MP_TAC THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "G" MATCH_MP_TAC; USE_THEN "H" MATCH_MP_TAC] THEN
    EXISTS_TAC `y:U->bool` THEN ASM SET_TAC[];
    SUBGOAL_THEN `{z | (v:U) INSERT z IN G INTER H} =
                  {z | v INSERT z IN G} INTER {z | v INSERT z IN H}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN USE_THEN "IH" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "G" MATCH_MP_TAC; USE_THEN "H" MATCH_MP_TAC] THEN
    EXISTS_TAC `(v:U) INSERT y` THEN ASM SET_TAC[]]);;

let RANDOM_SUBSET_INDEP_DISJOINT = prove
 (`!p:A prob_space (R:A->U->bool) u c d G H.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
     FINITE c /\ c SUBSET u /\ FINITE d /\ d SUBSET u /\ DISJOINT c d
     ==> prob p {x | x IN prob_carrier p /\
                     R x INTER c IN G /\ R x INTER d IN H} =
         prob p {x | x IN prob_carrier p /\ R x INTER c IN G} *
         prob p {x | x IN prob_carrier p /\ R x INTER d IN H}`,
  REPEAT STRIP_TAC THEN
  SPEC_TAC(`G:(U->bool)->bool`,`G:(U->bool)->bool`) THEN
  UNDISCH_TAC `DISJOINT (c:U->bool) d` THEN
  UNDISCH_TAC `(c:U->bool) SUBSET u` THEN
  UNDISCH_TAC `FINITE (c:U->bool)` THEN
  SPEC_TAC(`c:U->bool`,`c:U->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTER_EMPTY] THEN
    ASM_CASES_TAC `({}:U->bool) IN G` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; PROB_EMPTY; PROB_SPACE; REAL_MUL_LZERO;
                    REAL_MUL_LID; SET_RULE `{x | x IN (s:A->bool)} = s`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:U`; `c:U->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET; DISJOINT_INSERT] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "IH" (LABEL_TAC "IH" o
    C MP (ASSUME `DISJOINT (c:U->bool) d`) o
    C MP (ASSUME `(c:U->bool) SUBSET u`)) THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ R x INTER (v INSERT c) IN G /\
         R x INTER d IN H} =
    {x | x IN prob_carrier p /\
         (R:A->U->bool) x INTER (v INSERT (c UNION d)) IN
         {z | z INTER (v INSERT c) IN G /\ z INTER d IN H}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    SUBGOAL_THEN
     `((R:A->U->bool) x INTER (v INSERT (c UNION d))) INTER (v INSERT c) =
      R x INTER (v INSERT c) /\
      (R x INTER (v INSERT (c UNION d))) INTER d = R x INTER d`
    (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`;
                 `c UNION d:U->bool`; `v:U`] RANDOM_SUBSET_STEP_PROB) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `c:U->bool`;
                 `v:U`] RANDOM_SUBSET_STEP_PROB) THEN
  ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET; IN_UNION] THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  SUBGOAL_THEN
   `!x. (v INSERT ((R:A->U->bool) x INTER (c UNION d))) INTER (v INSERT c) =
        v INSERT (R x INTER c) /\
        (v INSERT (R x INTER (c UNION d))) INTER d = R x INTER d /\
        (R x INTER (c UNION d)) INTER (v INSERT c) = R x INTER c /\
        (R x INTER (c UNION d)) INTER d = R x INTER d`
  (fun th -> REWRITE_TAC[th; IN_ELIM_THM]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. {x | x IN prob_carrier p /\ v INSERT ((R:A->U->bool) x INTER c) IN K /\
             R x INTER d IN H} =
        {x | x IN prob_carrier p /\ R x INTER c IN {z | v INSERT z IN K} /\
             R x INTER d IN H} /\
        {x | x IN prob_carrier p /\ v INSERT ((R:A->U->bool) x INTER c) IN K} =
        {x | x IN prob_carrier p /\ R x INTER c IN {z | v INSERT z IN K}}`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  USE_THEN "IH" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_ACCEPT_TAC(REAL_RING
   `!a b c h:real. a * b * h + (&1 - a) * c * h
     = (a * b + (&1 - a) * c) * h`));;

let HARRIS_INEQUALITY_DOWN = prove
 (`!p:A prob_space (R:A->U->bool) u t G H.
    indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
    FINITE t /\ t SUBSET u /\
    (!y z. y IN G /\ y SUBSET z /\ z SUBSET t ==> z IN G) /\
    (!y z. y IN H /\ y SUBSET z /\ z SUBSET t ==> z IN H)
    ==> prob p {x | x IN prob_carrier p /\
                    R x INTER t IN G /\ ~(R x INTER t IN H)}
        <= prob p {x | x IN prob_carrier p /\ R x INTER t IN G} *
           prob p {x | x IN prob_carrier p /\ ~(R x INTER t IN H)} /\
        prob p {x | x IN prob_carrier p /\ ~(R x INTER t IN G)} *
        prob p {x | x IN prob_carrier p /\ ~(R x INTER t IN H)}
        <= prob p {x | x IN prob_carrier p /\
                       ~(R x INTER t IN G) /\ ~(R x INTER t IN H)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HARRIS_INEQUALITY) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!K. {x | x IN prob_carrier p /\ (R:A->U->bool) x INTER t IN K}
        IN prob_events p`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN
    EXISTS_TAC `u:U->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `EG = {x | x IN prob_carrier p /\ (R:A->U->bool) x INTER t IN G}` THEN
  ABBREV_TAC
   `EH = {x | x IN prob_carrier p /\ (R:A->U->bool) x INTER t IN H}` THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ (R:A->U->bool) x INTER t IN G /\
         R x INTER t IN H} = EG INTER EH /\
    {x | x IN prob_carrier p /\ R x INTER t IN G /\ ~(R x INTER t IN H)} =
    EG DIFF (EG INTER EH) /\
    {x | x IN prob_carrier p /\
       ~(R x INTER t IN H)} = prob_carrier p DIFF EH /\
    {x | x IN prob_carrier p /\
       ~(R x INTER t IN G)} = prob_carrier p DIFF EG /\
    {x | x IN prob_carrier p /\ ~(R x INTER t IN G) /\ ~(R x INTER t IN H)} =
    prob_carrier p DIFF (EG UNION EH)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["EG"; "EH"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `EG IN prob_events (p:A prob_space) /\ EH IN prob_events p`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["EG"; "EH"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_COMPL; PROB_DIFF_SUBSET; PROB_INTER_IN_EVENTS;
               PROB_UNION_IN_EVENTS; PROB_UNION; INTER_SUBSET] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

let JANSON_DELTA_INSERT = prove
 (`!(f:K->K->real) r s i.
     FINITE s /\ ~(i IN s) /\ (!j k. r j k <=> r k j) /\ (!j k. f j k = f k j)
     ==> sum (i INSERT s)
             (\k. sum {j | j IN i INSERT s /\ ~(j = k) /\ r k j} (\j. f k j)) =
         sum s (\k. sum {j | j IN s /\ ~(j = k) /\ r k j} (\j. f k j)) +
         &2 * sum {j | j IN s /\ r i j} (\j. f i j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
  SUBGOAL_THEN
   `{j | j IN i INSERT s /\ ~(j = i) /\ r i j} =
    {j | j IN s /\ (r:K->K->bool) i j}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN s
        ==> sum {j | j IN i INSERT s /\ ~(j = k) /\ r j k}
                (\x. (f:K->K->real) k x) =
            sum {j | j IN s /\ ~(j = k) /\ r j k} (\x. f k x) +
            (if r i k then f i k else &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `(r:K->K->bool) i k` THEN
    ASM_REWRITE_TAC[REAL_ADD_RID] THENL
     [SUBGOAL_THEN
       `{j | j IN i INSERT s /\ ~(j = k) /\ r j k} =
        i INSERT {j | j IN s /\ ~(j = k) /\ (r:K->K->bool) j k}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
       X_GEN_TAC `j:K` THEN
        ASM_CASES_TAC `j:K = i` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RESTRICT; IN_ELIM_THM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[SPECL [`k:K`; `i:K`] th]) THEN
      MATCH_ACCEPT_TAC REAL_ADD_SYM;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
      X_GEN_TAC `j:K` THEN ASM_CASES_TAC `j:K = i` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum s (\x. sum {j | j IN i INSERT s /\ ~(j = x) /\ r j x}
                   (\x'. (f:K->K->real) x x')) =
    sum s (\x. sum {j | j IN s /\ ~(j = x) /\ r j x} (\x'. f x x')) +
    sum {j | j IN s /\ r i j} (\j. f i j)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_RESTRICT_SET; GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[];
    MATCH_ACCEPT_TAC(REAL_ARITH `!a b:real. a + b + a = b + &2 * a`)]);;

let RANDOM_SUBSET_HARRIS_AVOID = prove
 (`!p:A prob_space (R:A->U->bool) u c K (a:K->U->bool) G W.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
     FINITE c /\ c SUBSET u /\
     (!y z. y IN K /\ y SUBSET z /\ z SUBSET c ==> z IN K) /\ FINITE W /\
     (!j. j IN W ==> FINITE (a j) /\ a j SUBSET u /\
                     (!y z. y IN G j /\ y SUBSET z /\ z SUBSET a j
                        ==> z IN G j))
     ==> prob p {x | x IN prob_carrier p /\ R x INTER c IN K /\
                     !j. j IN W ==> ~(R x INTER a j IN G j)}
         <= prob p {x | x IN prob_carrier p /\ R x INTER c IN K} *
            prob p {x | x IN prob_carrier p /\
                        !j. j IN W ==> ~(R x INTER a j IN G j)} /\
         prob p {x | x IN prob_carrier p /\ ~(R x INTER c IN K)} *
         prob p {x | x IN prob_carrier p /\
                     !j. j IN W ==> ~(R x INTER a j IN G j)}
         <= prob p {x | x IN prob_carrier p /\ ~(R x INTER c IN K) /\
                        !j. j IN W ==> ~(R x INTER a j IN G j)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t = c UNION UNIONS (IMAGE (a:K->U->bool) W)` THEN
  SUBGOAL_THEN
   `FINITE (t:U->bool) /\ t SUBSET u /\ c SUBSET t /\
    (!j. j IN W ==> (a:K->U->bool) j SUBSET t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 UNION_SUBSET; UNIONS_SUBSET] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ((R:A->U->bool) x INTER t) INTER c = R x INTER c /\
        (!j. j IN W ==> (R x INTER t) INTER (a:K->U->bool) j = R x INTER a j)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `t:U->bool`;
                 `{z | z INTER c IN (K:(U->bool)->bool)}`;
                 `{z | ?j. j IN W /\ z INTER (a:K->U->bool) j IN G j}`]
    HARRIS_INEQUALITY_DOWN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        free_in `K:(U->bool)->bool` (concl th) && is_forall (concl th))) THEN
      EXISTS_TAC `y INTER c:U->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `j:K` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:K` o check (fun th ->
        free_in `G:K->(U->bool)->bool` (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `y INTER (a:K->U->bool) j` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  ASM_SIMP_TAC[]);;

let RANDOM_SUBSET_INDEP_AVOID = prove
 (`!p:A prob_space (R:A->U->bool) u c K (a:K->U->bool) G W.
     indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
     FINITE c /\ c SUBSET u /\ FINITE W /\
     (!j. j IN W ==> FINITE (a j) /\ a j SUBSET u /\ DISJOINT c (a j))
     ==> prob p {x | x IN prob_carrier p /\ R x INTER c IN K /\
                     !j. j IN W ==> ~(R x INTER a j IN G j)} =
         prob p {x | x IN prob_carrier p /\ R x INTER c IN K} *
         prob p {x | x IN prob_carrier p /\
                     !j. j IN W ==> ~(R x INTER a j IN G j)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = UNIONS (IMAGE (a:K->U->bool) W)` THEN
  SUBGOAL_THEN
   `FINITE (d:U->bool) /\ d SUBSET u /\ DISJOINT c d /\
    (!j. j IN W ==> (a:K->U->bool) j SUBSET d)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 UNIONS_SUBSET] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x j. j IN W
          ==> ((R:A->U->bool) x INTER d) INTER (a:K->U->bool) j
            = R x INTER a j`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `c:U->bool`;
                 `d:U->bool`; `K:(U->bool)->bool`;
                 `{z | !j. j IN W ==> ~(z INTER (a:K->U->bool) j IN G j)}`]
    RANDOM_SUBSET_INDEP_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

let RANDOM_SUBSET_AVOID_REP = prove
 (`!p:A prob_space (R:A->U->bool) (a:K->U->bool) G W t.
     (!j. j IN W ==> a j SUBSET t)
     ==> {x | x IN prob_carrier p /\ !j. j IN W ==> ~(R x INTER a j IN G j)} =
         {x | x IN prob_carrier p /\
              ~(R x INTER t IN {z | ?j. j IN W /\ z INTER a j IN G j})}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM;
                                    NOT_EXISTS_THM] THEN
  X_GEN_TAC `x:A` THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `(j:K) IN W` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((R:A->U->bool) x INTER t) INTER a (j:K) = R x INTER a j`
    (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[]);;

let RANDOM_SUBSET_AVOID_IN_EVENTS = prove
 (`!p:A prob_space (R:A->U->bool) u (a:K->U->bool) G W.
     (!v. v IN u ==> {x | x IN prob_carrier p /\ v IN R x} IN prob_events p) /\
     FINITE W /\ (!j. j IN W ==> FINITE (a j) /\ a j SUBSET u)
     ==> {x | x IN prob_carrier p /\ !j. j IN W ==> ~(R x INTER a j IN G j)}
         IN prob_events p`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = UNIONS (IMAGE (a:K->U->bool) W)` THEN
  SUBGOAL_THEN
   `FINITE (d:U->bool) /\ d SUBSET u /\
    (!j. j IN W ==> (a:K->U->bool) j SUBSET d)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 UNIONS_SUBSET] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `a:K->U->bool`;
                 `G:K->(U->bool)->bool`; `W:K->bool`; `d:U->bool`]
    RANDOM_SUBSET_AVOID_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | x IN (s:A->bool) /\ ~P x} = s DIFF {x | x IN s /\ P x}`] THEN
  MATCH_MP_TAC PROB_COMPL_IN_EVENTS THEN
  MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN EXISTS_TAC `u:U->bool` THEN
  ASM_REWRITE_TAC[]);;

let JANSON_STEP = prove
 (`!p:A prob_space (R:A->U->bool) u (a:K->U->bool) G S i.
  indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
  FINITE S /\
  (!j. j IN i INSERT S
       ==> FINITE (a j) /\ a j SUBSET u /\
           (!y z. y IN G j /\ y SUBSET z /\ z SUBSET a j ==> z IN G j))
  ==> prob p {x | x IN prob_carrier p /\
                  !j. j IN i INSERT S ==> ~(R x INTER a j IN G j)}
      <= prob p {x | x IN prob_carrier p /\
                     !j. j IN S ==> ~(R x INTER a j IN G j)} *
         (&1 - prob p {x | x IN prob_carrier p /\ R x INTER a i IN G i} +
          sum {j | j IN S /\ ~DISJOINT (a i) (a j)}
              (\j. prob p ({x | x IN prob_carrier p /\ R x INTER a i IN G i}
                           INTER
                           {x | x IN prob_carrier p /\
                              R x INTER a j IN G j})))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "S")))) THEN
  ABBREV_TAC `S1 = {j | j IN S /\ ~DISJOINT ((a:K->U->bool) i) (a j)}` THEN
  ABBREV_TAC `S2 = {j | j IN S /\ DISJOINT ((a:K->U->bool) i) (a j)}` THEN
  SUBGOAL_THEN
   `FINITE (S1:K->bool) /\ FINITE (S2:K->bool) /\ S1 SUBSET S /\ S2 SUBSET S`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; SUBSET_RESTRICT];
    ALL_TAC] THEN
  ABBREV_TAC
   `Ei = {x | x IN prob_carrier p /\
      (R:A->U->bool) x INTER a (i:K) IN G i}` THEN
  ABBREV_TAC
   `DS = {x | x IN prob_carrier p /\
              !j. j IN S ==> ~((R:A->U->bool) x INTER (a:K->U->bool) j
                IN G j)}` THEN
  ABBREV_TAC
   `DS2 = {x | x IN prob_carrier p /\
               !j. j IN S2
               ==> ~((R:A->U->bool) x INTER (a:K->U->bool) j IN G j)}` THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\
         ~((R:A->U->bool) x INTER (a:K->U->bool) i IN G i) /\
         (!j. j IN S ==> ~(R x INTER a j IN G j))} =
    DS DIFF (Ei INTER DS)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["DS"; "Ei"] THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN u
        ==> {x | x IN prob_carrier p /\
           v IN (R:A->U->bool) x} IN prob_events p`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
     GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Ei IN prob_events p /\ DS IN prob_events p /\ DS2 IN prob_events p /\
    (!j. j IN S
         ==> {x | x IN prob_carrier p /\
                  (R:A->U->bool) x INTER (a:K->U->bool) j IN G j}
             IN prob_events p)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Ei"; "DS"; "DS2"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN ASM_MESON_TAC[];
      MATCH_MP_TAC RANDOM_SUBSET_AVOID_IN_EVENTS THEN ASM_MESON_TAC[];
      MATCH_MP_TAC RANDOM_SUBSET_AVOID_IN_EVENTS THEN ASM_MESON_TAC[SUBSET];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `prob p ((Ei:A->bool) INTER DS2) = prob p Ei * prob p DS2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`;
                   `(a:K->U->bool) i`; `(G:K->(U->bool)->bool) i`;
                   `a:K->U->bool`; `G:K->(U->bool)->bool`; `S2:K->bool`]
      RANDOM_SUBSET_INDEP_AVOID) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(j:K) IN S /\ DISJOINT ((a:K->U->bool) i) (a j)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(j:K) IN S2` THEN EXPAND_TAC "S2" THEN
        SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      USE_THEN "S" (MP_TAC o SPEC `j:K`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Ei"; "DS2"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN S1
        ==> prob p ((Ei:A->bool) INTER
                    {x | x IN prob_carrier p /\
                         (R:A->U->bool) x INTER (a:K->U->bool) j IN G j}
                    INTER DS2)
            <= prob p (Ei INTER {x | x IN prob_carrier p /\
                                     R x INTER a j IN G j}) *
               prob p DS2`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(j:K) IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "S" (fun th ->
      STRIP_ASSUME_TAC(MP (SPEC `j:K` th) (ASSUME `(j:K) IN S`))) THEN
    MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`;
                   `(a:K->U->bool) i UNION a j`;
                   `{z | z INTER (a:K->U->bool) i IN G i /\
                      z INTER a j IN G j}`;
                   `a:K->U->bool`; `G:K->(U->bool)->bool`; `S2:K->bool`]
      RANDOM_SUBSET_HARRIS_AVOID) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET; IN_ELIM_THM] THEN
     CONJ_TAC THENL
       [REPEAT STRIP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            free_in `(a:K->U->bool) i` (concl th) &&
            is_forall (concl th))) THEN
          EXISTS_TAC `y INTER (a:K->U->bool) i` THEN ASM SET_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            free_in `(a:K->U->bool) j` (concl th) &&
            is_forall (concl th))) THEN
          EXISTS_TAC `y INTER (a:K->U->bool) j` THEN ASM SET_TAC[]];
        X_GEN_TAC `k:K` THEN DISCH_TAC THEN USE_THEN "S" MATCH_MP_TAC THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MAP_EVERY EXPAND_TAC ["Ei"; "DS2"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `!x. ((R:A->U->bool) x INTER (a i UNION a j)) INTER (a:K->U->bool) i =
          R x INTER a i /\
          (R x INTER (a i UNION a j)) INTER a j = R x INTER a j`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [AP_TERM_TAC; BINOP_TAC THEN AP_TERM_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `prob p ((Ei:A->bool) INTER DS2) <=
    prob p (Ei INTER DS) +
    sum S1 (\j. prob p (Ei INTER
                        {x | x IN prob_carrier p /\
                             (R:A->U->bool) x INTER (a:K->U->bool) j IN G j}
                        INTER DS2))`
  ASSUME_TAC THENL
   [ABBREV_TAC
     `Fj = \j. (Ei:A->bool) INTER
               {x | x IN prob_carrier p /\
                    (R:A->U->bool) x INTER (a:K->U->bool) j
                      IN G j} INTER DS2` THEN
    SUBGOAL_THEN `!j. j IN S1 ==> (Fj:K->A->bool) j IN prob_events p`
    ASSUME_TAC THENL
     [EXPAND_TAC "Fj" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS (IMAGE (Fj:K->A->bool) S1) IN prob_events p`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p (((Ei:A->bool) INTER DS) UNION
                        UNIONS (IMAGE (Fj:K->A->bool) S1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN
      ASM_SIMP_TAC[PROB_INTER_IN_EVENTS; PROB_UNION_IN_EVENTS] THEN
      MAP_EVERY EXPAND_TAC ["Fj"; "DS"; "DS2"; "S1"; "S2"] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE;
                  IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `prob p ((Ei:A->bool) INTER DS) +
                prob p (UNIONS (IMAGE (Fj:K->A->bool) S1))` THEN
    ASM_SIMP_TAC[PROB_SUBADDITIVE; PROB_INTER_IN_EVENTS; REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (Fj:K->A->bool) S1) (prob p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PROB_SUBADDITIVE_FINITE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
    ASM_SIMP_TAC[PROB_POSITIVE; o_DEF] THEN EXPAND_TAC "Fj" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PROB_DIFF_SUBSET; PROB_INTER_IN_EVENTS; INTER_SUBSET] THEN
  SUBGOAL_THEN
   `sum S1 (\j. prob p ((Ei:A->bool) INTER
                        {x | x IN prob_carrier p /\
                             (R:A->U->bool) x INTER (a:K->U->bool) j IN G j}
                        INTER DS2))
    <= sum S1 (\j. prob p (Ei INTER {x | x IN prob_carrier p /\
                                         R x INTER a j IN G j})) *
       prob p DS2`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prob p (DS:A->bool) <= prob p DS2` MP_TAC THENL
   [MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["DS"; "DS2"] THEN REWRITE_TAC[SUBSET;
                                                        IN_ELIM_THM] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(Ei:A->bool) INTER DS`] PROB_POSITIVE) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `DS:A->bool`] PROB_POSITIVE) THEN
  ASM_SIMP_TAC[PROB_INTER_IN_EVENTS] THEN
  UNDISCH_TAC
   `prob p ((Ei:A->bool) INTER DS2) <=
    prob p (Ei INTER DS) +
    sum S1 (\j. prob p (Ei INTER
                        {x | x IN prob_carrier p /\
                             (R:A->U->bool) x INTER (a:K->U->bool) j IN G j}
                        INTER DS2))` THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`sum S1 (\j. prob p ((Ei:A->bool) INTER
                                {x | x IN prob_carrier p /\
                                     (R:A->U->bool) x INTER (a:K->U->bool) j
                                     IN G j} INTER DS2))`, `tt:real`) THEN
  SPEC_TAC(`sum S1 (\j. prob p ((Ei:A->bool) INTER
                                {x | x IN prob_carrier p /\
                                     (R:A->U->bool) x INTER (a:K->U->bool) j
                                     IN G j}))`, `ss:real`) THEN
  SPEC_TAC(`prob p ((Ei:A->bool) INTER DS)`, `aa:real`) THEN
  SPEC_TAC(`prob p (DS:A->bool)`, `dd:real`) THEN
  SPEC_TAC(`prob p (DS2:A->bool)`, `d2:real`) THEN
  SPEC_TAC(`prob p (Ei:A->bool)`, `bb:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= bb - ss` THENL
   [MP_TAC(SPECL [`d2 - dd:real`; `bb - ss:real`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`dd:real`; `ss - bb:real`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC]);;

let JANSON_EXP_BOUND = prove
 (`!b e s. &0 <= b /\ b <= e /\ e < &1 /\ &0 <= s
           ==> &1 - b + s <= (&1 - b) * exp(s / (&1 - e))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - b) * (&1 + s / (&1 - e))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `s <= ((&1 - b) * s) / (&1 - e)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      MP_TAC(SPECL [`s:real`; `&1 - e`; `&1 - b`] REAL_LE_LMUL) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
    ASM_REAL_ARITH_TAC]);;

let JANSON_BOUNDS = prove
 (`!p:A prob_space (R:A->U->bool) u (a:K->U->bool) G e s.
    indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
    e < &1 /\ FINITE s /\
    (!i. i IN s
         ==> FINITE (a i) /\ a i SUBSET u /\
             (!y z. y IN G i /\ y SUBSET z /\ z SUBSET a i ==> z IN G i) /\
             prob p {x | x IN prob_carrier p /\ R x INTER a i IN G i} <= e)
    ==> product s (\i. &1 - prob p {x | x IN prob_carrier p /\
                                        R x INTER a i IN G i})
        <= prob p {x | x IN prob_carrier p /\
                       !i. i IN s ==> ~(R x INTER a i IN G i)} /\
        prob p {x | x IN prob_carrier p /\
                    !i. i IN s ==> ~(R x INTER a i IN G i)}
        <= product s (\i. &1 - prob p {x | x IN prob_carrier p /\
                                           R x INTER a i IN G i}) *
           exp(sum s (\i. sum {j | j IN s /\ ~(j = i) /\ ~DISJOINT (a i) (a j)}
                              (\j. prob p ({x | x IN prob_carrier p /\
                                                R x INTER a i IN G i} INTER
                                           {x | x IN prob_carrier p /\
                                                R x INTER a j IN G j}))) /
               (&2 - &2 * e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  SUBGOAL_THEN
   `!v. v IN u
        ==> {x | x IN prob_carrier p /\
           v IN (R:A->U->bool) x} IN prob_events p`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
     GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`s:K->bool`,`s:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES; SUM_CLAUSES; real_div;
                REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_RID; PROB_SPACE;
                SET_RULE `{x | x IN (s:A->bool)} = s`; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `W:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  REMOVE_THEN "IH" MP_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `j:K` THEN DISCH_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN
    ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LO") (LABEL_TAC "UP"))] THEN
  USE_THEN "H" (fun th ->
    STRIP_ASSUME_TAC (REWRITE_RULE[IN_INSERT] (SPEC `i:K` th))) THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`;
                 `(a:K->U->bool) i`; `(G:K->(U->bool)->bool) i`;
                 `a:K->U->bool`; `G:K->(U->bool)->bool`; `W:K->bool`]
    RANDOM_SUBSET_HARRIS_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    USE_THEN "H" (MP_TAC o SPEC `j:K`) THEN ASM_SIMP_TAC[IN_INSERT];
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `prob p {x | x IN prob_carrier p /\
                ~((R:A->U->bool) x INTER (a:K->U->bool) i IN G i)} =
    &1 - prob p {x | x IN prob_carrier p /\ R x INTER a i IN G i}`
  SUBST1_TAC THENL
   [REWRITE_TAC[SET_RULE
     `{x | x IN (s:A->bool) /\ ~P x} = s DIFF {x | x IN s /\ P x}`] THEN
    MATCH_MP_TAC PROB_COMPL THEN
    MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `(&1 - prob p {x | x IN prob_carrier p /\
                        (R:A->U->bool) x INTER (a:K->U->bool) i IN G i}) *
      prob p {x | x IN prob_carrier p /\
                  !j. j IN W ==> ~(R x INTER a j IN G j)}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 <= &1 - x`) THEN
    MATCH_MP_TAC PROB_LE_1 THEN
    MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\j k. prob p ({x | x IN prob_carrier p /\
                         (R:A->U->bool) x INTER (a:K->U->bool) j IN G j} INTER
                    {x | x IN prob_carrier p /\ R x INTER a k IN G k})`;
     `\j k. ~DISJOINT ((a:K->U->bool) j) (a k)`; `W:K->bool`; `i:K`]
    JANSON_DELTA_INSERT)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DISJOINT_SYM; INTER_COMM];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `a:K->U->bool`;
                 `G:K->(U->bool)->bool`; `W:K->bool`; `i:K`] JANSON_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "H" (MP_TAC o SPEC `j:K`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= sum {j | j IN W /\ ~DISJOINT ((a:K->U->bool) i) (a j)}
     (\j. prob p ({x | x IN prob_carrier p /\
                       (R:A->U->bool) x INTER a i IN G i} INTER
                  {x | x IN prob_carrier p /\ R x INTER a j IN G j}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_RESTRICT;
                                              IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_POSITIVE THEN
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THEN
    MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN EXISTS_TAC `u:U->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "H" (MP_TAC o SPEC `j:K`) THEN
    ASM_SIMP_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= prob p {x | x IN prob_carrier p /\
                      !j. j IN W
                          ==> ~((R:A->U->bool) x INTER (a:K->U->bool) j
                                IN G j)} /\
    &0 <= prob p {x | x IN prob_carrier p /\ R x INTER a i IN G i}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PROB_POSITIVE THENL
     [MATCH_MP_TAC RANDOM_SUBSET_AVOID_IN_EVENTS THEN
     EXISTS_TAC `u:U->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      USE_THEN "H" (MP_TAC o SPEC `j:K`) THEN ASM_SIMP_TAC[IN_INSERT];
      MATCH_MP_TAC RANDOM_SUBSET_EVENT_IN_EVENTS THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`prob p {x | x IN prob_carrier p /\
                 (R:A->U->bool) x INTER (a:K->U->bool) i IN G i}`;
    `e:real`;
    `sum {j | j IN W /\ ~DISJOINT ((a:K->U->bool) i) (a j)}
       (\j. prob p ({x | x IN prob_carrier p /\
                         (R:A->U->bool) x INTER a i IN G i} INTER
                    {x | x IN prob_carrier p /\ R x INTER a j IN G j}))`]
   JANSON_EXP_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `prob p {x | x IN prob_carrier p /\
                ~((R:A->U->bool) x INTER (a:K->U->bool) i IN G i) /\
                (!j. j IN W ==> ~(R x INTER a j IN G j))} <=
    prob p {x | x IN prob_carrier p /\
                (!j. j IN W ==> ~(R x INTER a j IN G j))} *
    (&1 - prob p {x | x IN prob_carrier p /\ R x INTER a i IN G i} +
     sum {j | j IN W /\ ~DISJOINT (a i) (a j)}
       (\j. prob p ({x | x IN prob_carrier p /\ R x INTER a i IN G i} INTER
                    {x | x IN prob_carrier p /\ R x INTER a j IN G j})))` THEN
  REMOVE_THEN "UP" MP_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`sum {j | j IN W /\ ~DISJOINT ((a:K->U->bool) i) (a j)}
             (\j. prob p ({x | x IN prob_carrier p /\
                               (R:A->U->bool) x INTER a i IN G i} INTER
                          {x | x IN prob_carrier p /\ R x INTER a j IN G j}))`,
           `sg:real`) THEN
  SPEC_TAC(`sum W (\k. sum {j | j IN W /\ ~(j = k) /\
                                ~DISJOINT ((a:K->U->bool) k) (a j)}
             (\j. prob p ({x | x IN prob_carrier p /\
                               (R:A->U->bool) x INTER a k IN G k} INTER
                          {x | x IN prob_carrier p /\
                               R x INTER a j IN G j})))`, `dl:real`) THEN
  SPEC_TAC(`product W (\i. &1 - prob p {x | x IN prob_carrier p /\
                                            (R:A->U->bool) x INTER
                                            (a:K->U->bool) i IN G i})`,
           `pw:real`) THEN
  SPEC_TAC(`prob p {x | x IN prob_carrier p /\
                        (R:A->U->bool) x INTER (a:K->U->bool) i IN G i}`,
           `bb:real`) THEN
  SPEC_TAC(`prob p {x | x IN prob_carrier p /\
                        !j. j IN W ==> ~((R:A->U->bool) x INTER
                                         (a:K->U->bool) j IN G j)}`,
           `dd:real`) THEN
  SPEC_TAC(`prob p {x | x IN prob_carrier p /\
                        ~((R:A->U->bool) x INTER (a:K->U->bool) i IN G i) /\
                        (!j. j IN W ==> ~(R x INTER a j IN G j))}`,
           `d1:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(dl + &2 * sg) / (&2 - &2 * e) = dl / (&2 - &2 * e) + sg / (&1 - e)`
  SUBST1_TAC THENL [UNDISCH_TAC `e < &1` THEN CONV_TAC REAL_FIELD;
                    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  ABBREV_TAC `ex = exp(dl / (&2 - &2 * e))` THEN
  ABBREV_TAC `ey = exp(sg / (&1 - e))` THEN
  SUBGOAL_THEN `&0 <= (&1 - bb) * ey` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN EXPAND_TAC "ey" THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`dd:real`; `&1 - bb + sg`; `(&1 - bb) * ey`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`dd:real`; `pw * ex:real`; `(&1 - bb) * ey`] REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let JANSON_INEQUALITY_GEN = prove
 (`!p:A prob_space (R:A->U->bool) u (a:K->U->bool) G B s e.
    indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
    FINITE s /\
    (!i. i IN s
         ==> FINITE (a i) /\ a i SUBSET u /\
             (!y z. y IN G i /\ y SUBSET z /\ z SUBSET a i ==> z IN G i) /\
             B i = {x | x IN prob_carrier p /\ R x INTER a i IN G i} /\
             prob p (B i) <= e) /\
    e < &1
    ==> product s (\i. &1 - prob p (B i))
        <= prob p {x | x IN prob_carrier p /\ !i. i IN s ==> ~(x IN B i)} /\
        prob p {x | x IN prob_carrier p /\ !i. i IN s ==> ~(x IN B i)}
        <= product s (\i. &1 - prob p (B i)) *
           exp(sum s (\i. sum {j | j IN s /\ ~(j = i) /\ ~DISJOINT (a i) (a j)}
                              (\j. prob p (B i INTER B j))) /
               (&2 - &2 * e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `R:A->U->bool`; `u:U->bool`; `a:K->U->bool`;
                 `G:K->(U->bool)->bool`; `e:real`; `s:K->bool`]
    JANSON_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ !i. i IN s ==> ~(x IN (B:K->A->bool) i)} =
    {x | x IN prob_carrier p /\
         !i. i IN s
             ==> ~((R:A->U->bool) x INTER (a:K->U->bool) i IN G i)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `(x:A) IN prob_carrier p` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [BINOP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:K` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let JANSON_INEQUALITY = prove
 (`!p:A prob_space (R:A->U->bool) u (a:K->U->bool) B s e.
    indep_event_family p u (\v. {x | x IN prob_carrier p /\ v IN R x}) /\
    FINITE s /\
    (!i. i IN s
         ==> FINITE (a i) /\ a i SUBSET u /\
             B i = {x | x IN prob_carrier p /\ a i SUBSET R x} /\
             prob p (B i) <= e) /\
    e < &1
    ==> product s (\i. &1 - prob p (B i))
        <= prob p {x | x IN prob_carrier p /\ !i. i IN s ==> ~(x IN B i)} /\
        prob p {x | x IN prob_carrier p /\ !i. i IN s ==> ~(x IN B i)}
        <= product s (\i. &1 - prob p (B i)) *
           exp(sum s (\i. sum {j | j IN s /\ ~(j = i) /\ ~DISJOINT (a i) (a j)}
                              (\j. prob p (B i INTER B j))) /
               (&2 - &2 * e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC JANSON_INEQUALITY_GEN THEN
  MAP_EVERY EXISTS_TAC
   [`R:A->U->bool`; `u:U->bool`;
    `\i:K z:U->bool. (a:K->U->bool) i SUBSET z`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bridges for independent families of events: the library's                 *)
(* indep_events_seq is the case of the index set (:num), and a family of     *)
(* events is independent iff the indicators form an independent family of    *)
(* random variables.                                                         *)
(* ------------------------------------------------------------------------- *)

let INDEP_EVENT_FAMILY_SEQ = prove
 (`!p:A prob_space B. indep_events_seq p B <=> indep_event_family p (:num) B`,
  REWRITE_TAC[indep_events_seq; indep_event_family; SUBSET_UNIV; IN_UNIV]);;

let INDEP_EVENT_FAMILY_IMP_INDICATOR = prove
 (`!p:A prob_space (s:K->bool) E.
     indep_event_family p s E
     ==> indep_rv_family p s (\i. indicator_fn (E i))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [indep_event_family]) THEN
  REWRITE_TAC[indep_rv_family] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE; INTEGRABLE_INDICATOR];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:K->bool`; `z:K->real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTERS_IMAGE_CDF_EVENTS] THEN
  ABBREV_TAC `R = \x:A. {i:K | x IN E i}` THEN
  SUBGOAL_THEN
   `!v. v IN s
        ==> {x | x IN prob_carrier p /\ v IN (R:A->K->bool) x} = E v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `(E:K->A->bool) v`]
      PROB_EVENT_SUBSET) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `indep_event_family p s
     (\v. {x | x IN prob_carrier p /\ v IN (R:A->K->bool) x})`
  ASSUME_TAC THENL
   [UNDISCH_TAC `indep_event_family (p:A prob_space) (s:K->bool) E` THEN
    REWRITE_TAC[indep_event_family] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `w:K->bool` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!v. v IN w
            ==> {x | x IN prob_carrier p /\ v IN (R:A->K->bool) x} = E v`
      ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
       [AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. FINITE w
        ==> w SUBSET s
        ==> prob p {x | x IN prob_carrier p /\
                    (!i. i IN w
                         ==> indicator_fn ((E:K->A->bool) i) x <= z i)} =
            product w (\i. prob p {x | x IN prob_carrier p /\
                                       indicator_fn (E i) x <= z i})`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES; PROB_SPACE;
                SET_RULE `{x | x IN (s:A->bool)} = s`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:K`; `w:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  REMOVE_THEN "IH" (MP_TAC o C MP (ASSUME `(w:K->bool) SUBSET s`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`p:A prob_space`; `R:A->K->bool`; `s:K->bool`; `{v:K}`; `w:K->bool`;
    `{y | (if (v:K) IN y then &1 else &0) <= (z:K->real) v}`;
    `{y | !i. i IN w ==> (if (i:K) IN y then &1 else &0) <= (z:K->real) i}`]
   RANDOM_SUBSET_INDEP_DISJOINT) THEN
  ASM_REWRITE_TAC[FINITE_SING; SING_SUBSET] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "R" THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_SING; indicator_fn] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [AP_TERM_TAC; BINOP_TAC THEN AP_TERM_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; FORALL_IN_INSERT] THEN ASM_MESON_TAC[]);;

let INDEP_EVENT_FAMILY_COMPL_INDICATOR = prove
 (`!p:A prob_space (s:K->bool) E D.
     (!i. i IN s ==> E i IN prob_events p /\ D i = prob_carrier p DIFF E i) /\
     indep_rv_family p s (\i. indicator_fn (E i))
     ==> indep_event_family p s D`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN s
        ==> {x | x IN prob_carrier p /\
                 indicator_fn ((E:K->A->bool) i) x <= &1 / &2} = D i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; indicator_fn] THEN
    X_GEN_TAC `x:A` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[indep_rv_family; indep_event_family] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS]; ALL_TAC] THEN
  X_GEN_TAC `w:K->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:K->bool`; `\i:K. &1 / &2`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN ASM SET_TAC[];
    MATCH_MP_TAC PRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ASM SET_TAC[]]);;

let INDEP_EVENT_FAMILY_INDICATOR = prove
 (`!p:A prob_space (s:K->bool) E.
     indep_event_family p s E <=>
     (!i. i IN s ==> E i IN prob_events p) /\
     indep_rv_family p s (\i. indicator_fn (E i))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[INDEP_EVENT_FAMILY_IMP_INDICATOR] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
      GEN_REWRITE_RULE I [indep_event_family]) THEN
    REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `s:K->bool`; `E:K->A->bool`;
                 `\i:K. prob_carrier p DIFF (E:K->A->bool) i`]
    INDEP_EVENT_FAMILY_COMPL_INDICATOR) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INDEP_EVENT_FAMILY_IMP_INDICATOR) THEN
  DISCH_TAC THEN MATCH_MP_TAC INDEP_EVENT_FAMILY_COMPL_INDICATOR THEN
  EXISTS_TAC `\i:K. prob_carrier p DIFF (E:K->A->bool) i` THEN
  ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(E:K->A->bool) i`] PROB_EVENT_SUBSET) THEN
  ASM_SIMP_TAC[] THEN SET_TAC[]);;
