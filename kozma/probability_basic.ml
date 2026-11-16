(* ========================================================================= *)
(* Moment and tail inequalities for one random variable, and Bonferroni's    *)
(* inequalities, from L. Kozma, "Useful Inequalities" (v0.44).               *)
(* ========================================================================= *)

needs "Probability/clt.ml";;
needs "kozma/real_lemmas.ml";;

(* ------------------------------------------------------------------------- *)
(* General results about expectation, with almost-sure hypotheses; they      *)
(* belong in Probability/expectation.ml.                                     *)
(* ------------------------------------------------------------------------- *)

let EXPECTATION_AS_NONNEG_ZERO = prove
 (`!p:A prob_space f.
        integrable p f /\ almost_surely p {x | &0 <= f x} /\
        expectation p f = &0
        ==> almost_surely p {x | f x = &0}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. max ((f:A->real) x) (&0)) /\
                integrable p (\x. max (--f x) (&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
    ASM_SIMP_TAC[INTEGRABLE_NEG; INTEGRABLE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `expectation (p:A prob_space) (\x. max (--(f:A->real) x) (&0)) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_AE_ZERO THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | &0 <= (f:A->real) x}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `expectation (p:A prob_space) (\x. max ((f:A->real) x) (&0)) = &0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `expectation (p:A prob_space) (f:A->real) =
                  expectation p (\x. max (f x) (&0) - max (--f x) (&0))`
    MP_TAC THENL
     [MATCH_MP_TAC EXPECTATION_EXT THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[EXPECTATION_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. max ((f:A->real) x) (&0)`]
         EXPECTATION_NONNEG_ZERO_AE_ZERO) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x:A | max ((f:A->real) x) (&0) = &0} INTER {x | &0 <= f x}` THEN
  ASM_SIMP_TAC[ALMOST_SURELY_INTER; IN_INTER; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let INTEGRABLE_MUL_INDICATOR_NULL = prove
 (`!p:A prob_space g n.
        random_variable p g /\ null_event p n
        ==> integrable p (\x. g x * indicator_fn n x) /\
            expectation p (\x. g x * indicator_fn n x) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[null_event] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable (p:A prob_space) (\x. (g:A->real) x * indicator_fn n x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[integrable] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      ASM_SIMP_TAC[ETA_AX; INTEGRABLE_INDICATOR];
      EXISTS_TAC `&0` THEN X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `simple_expectation (p:A prob_space) (h:A->real) =
                    simple_expectation p (\x. h x * indicator_fn n x)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SIMPLE_EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN
        DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
        COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:A`)) THEN
        ASM_REWRITE_TAC[indicator_fn; REAL_MUL_RZERO; REAL_ABS_0] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MATCH_MP_TAC SIMPLE_EXPECTATION_NULL_SET THEN ASM_REWRITE_TAC[]]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EXPECTATION_AE_ZERO THEN
    ASM_REWRITE_TAC[almost_surely] THEN EXISTS_TAC `n:A->bool` THEN
    ASM_REWRITE_TAC[null_event; SUBSET; IN_ELIM_THM; indicator_fn] THEN
    MESON_TAC[REAL_MUL_RZERO]]);;

let EXPECTATION_AS_EQ = prove
 (`!p:A prob_space f g.
        integrable p f /\ random_variable p g /\
        almost_surely p {x | f x = g x}
        ==> integrable p g /\ expectation p g = expectation p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC o
                GEN_REWRITE_RULE I [almost_surely]) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. (g:A->real) x - (f:A->real) x`;
                 `n:A->bool`] INTEGRABLE_MUL_INDICATOR_NULL) THEN
  ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; INTEGRABLE_IMP_RANDOM_VARIABLE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. x IN prob_carrier p
                      ==> (g:A->real) x =
                          (\x. f x + (g x - f x) * indicator_fn n x) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integrable (p:A prob_space)
      (\x. (f:A->real) x + ((g:A->real) x - f x) * indicator_fn n x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CARRIER_AGREE THEN
    EXISTS_TAC
     `\x. (f:A->real) x + ((g:A->real) x - f x) * indicator_fn n x` THEN
    ASM_REWRITE_TAC[];
    TRANS_TAC EQ_TRANS
     `expectation (p:A prob_space)
        (\x. (f:A->real) x + ((g:A->real) x - f x) * indicator_fn n x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_EXT THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`;
                     `\x. ((g:A->real) x - (f:A->real) x) * indicator_fn n x`]
             EXPECTATION_ADD) THEN
      ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC]]);;

let INTEGRABLE_AS_DOMINATED = prove
 (`!p:A prob_space f h.
        random_variable p f /\ integrable p h /\
        almost_surely p {x | abs(f x) <= h x}
        ==> integrable p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC o
              GEN_REWRITE_RULE I [almost_surely]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
  SUBGOAL_THEN `n IN prob_events (p:A prob_space)` ASSUME_TAC THENL
   [ASM_MESON_TAC[null_event]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                 `\x. (f:A->real) x * (&1 - indicator_fn n x)`; `f:A->real`]
         EXPECTATION_AS_EQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN EXISTS_TAC `h:A->real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
      REWRITE_TAC[RANDOM_VARIABLE_CONST] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
      ASM_SIMP_TAC[ETA_AX; INTEGRABLE_INDICATOR];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[indicator_fn] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ABS_0; REAL_ABS_POS;
                  REAL_SUB_RZERO; REAL_MUL_RID] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[almost_surely] THEN EXISTS_TAC `n:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; indicator_fn] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let INTEGRABLE_AS_BOUNDED = prove
 (`!p:A prob_space f M.
        random_variable p f /\ almost_surely p {x | abs(f x) <= M}
        ==> integrable p f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_DOMINATED THEN
  EXISTS_TAC `\x:A. M:real` THEN ASM_REWRITE_TAC[INTEGRABLE_CONST]);;

let EXPECTATION_IN_REALINTERVAL = prove
 (`!p:A prob_space X s.
        is_realinterval s /\ integrable p X /\ almost_surely p {x | X x IN s}
        ==> expectation p X IN s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = expectation (p:A prob_space) (X:A->real)` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ALMOST_SURELY_NONEMPTY) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(m:real) IN s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(!y. y IN s ==> y < m) \/ (!y. y IN s ==> m < y:real)`
    MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [is_realinterval]) THEN
    UNDISCH_TAC `~((m:real) IN s)` THEN UNDISCH_TAC `(X:A->real) x0 IN s` THEN
    MESON_TAC[REAL_LT_TOTAL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  let prv = MATCH_MP_TAC EXPECTATION_AS_NONNEG_ZERO THEN REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
       MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
       EXISTS_TAC `{x:A | (X:A->real) x IN s}` THEN
       ASM_SIMP_TAC[IN_ELIM_THM; REAL_SUB_LE; REAL_LT_IMP_LE];
       ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_CONST; EXPECTATION_CONST] THEN
       REAL_ARITH_TAC]
  and fin = DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ALMOST_SURELY_NONEMPTY o
      MATCH_MP ALMOST_SURELY_INTER o
      CONJ (ASSUME `almost_surely p {x:A | (X:A->real) x IN s}`)) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_SUB_0] in
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `almost_surely p {x:A | m - (X:A->real) x = &0}` MP_TAC THENL
     [prv; fin];
    SUBGOAL_THEN `almost_surely p {x:A | (X:A->real) x - m = &0}` MP_TAC THENL
     [prv; fin]]);;

let MARKOV_EVENT_INEQUALITY = prove
 (`!p:A prob_space f A s.
        integrable p f /\ almost_surely p {x | &0 <= f x} /\
        A IN prob_events p /\ almost_surely p {x | x IN A ==> s <= f x}
        ==> s * prob p A <= expectation p f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable (p:A prob_space) (\x. s * indicator_fn A x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_SIMP_TAC[ETA_AX; INTEGRABLE_INDICATOR];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `expectation (p:A prob_space) (\x. s * indicator_fn A x)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `s:real`; `indicator_fn (A:A->bool)`]
           EXPECTATION_CMUL) THEN
    ASM_SIMP_TAC[INTEGRABLE_INDICATOR; EXPECTATION_INDICATOR; REAL_LE_REFL];
    MATCH_MP_TAC EXPECTATION_MONO_AE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
     `{x:A | &0 <= (f:A->real) x} INTER {x | x IN A ==> s <= f x}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_INTER; IN_INTER; IN_ELIM_THM; indicator_fn] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let EXPECTATION_CAUCHY_SCHWARZ_EVENT = prove
 (`!p:A prob_space X A.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        A IN prob_events p
        ==> expectation p (\x. X x * indicator_fn A x) pow 2 <=
            expectation p (\x. X x pow 2) * prob p A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. indicator_fn A x pow 2 = indicator_fn A x`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[indicator_fn] THEN COND_CASES_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `indicator_fn (A:A->bool)`]
         EXPECTATION_CAUCHY_SCHWARZ) THEN
  ASM_SIMP_TAC[INTEGRABLE_POW2_IMP; INTEGRABLE_INDICATOR; ETA_AX;
               INTEGRABLE_MUL_INDICATOR_FN; EXPECTATION_INDICATOR]);;

(* ------------------------------------------------------------------------- *)
(* Hoelder's inequality for expectation: E|fg| <= (E|f|^a)^(1/a)             *)
(* (E|g|^b)^(1/b) for 1/a + 1/b = 1, by Young's inequality applied           *)
(* pointwise after scaling f and g by their norms.                           *)
(* ------------------------------------------------------------------------- *)

let EXPECTATION_HOELDER = prove
 (`!p:A prob_space f g a b.
        random_variable p f /\ random_variable p g /\
        &0 < a /\ &0 < b /\ inv a + inv b = &1 /\
        integrable p (\x. abs(f x) rpow a) /\
        integrable p (\x. abs(g x) rpow b)
        ==> integrable p (\x. f x * g x) /\
            expectation p (\x. abs(f x * g x)) <=
            expectation p (\x. abs(f x) rpow a) rpow inv a *
            expectation p (\x. abs(g x) rpow b) rpow inv b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable (p:A prob_space) (\x. (f:A->real) x * (g:A->real) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x. inv a * abs((f:A->real) x) rpow a +
                    inv b * abs((g:A->real) x) rpow b` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_MUL; INTEGRABLE_ADD; INTEGRABLE_CMUL] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`abs((f:A->real) x)`; `abs((g:A->real) x)`; `a:real`;
                   `b:real`] YOUNG_INEQUALITY) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z /\ &0 <= z ==> x <= y ==> x <= abs z`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; RPOW_POS_LE; REAL_ABS_POS]];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_ABS) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!h k c. &0 < c /\ integrable p (\x. abs((h:A->real) x) rpow c) /\
            expectation p (\x. abs(h x) rpow c) = &0 /\
            integrable p (\x. abs(h x) * abs((k:A->real) x))
            ==> expectation p (\x. abs(h x) * abs(k x)) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EXPECTATION_AE_ZERO THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x. abs((h:A->real) x) rpow c`]
           EXPECTATION_AS_NONNEG_ZERO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN
      SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
      DISCH_TAC] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | abs((h:A->real) x) rpow c = &0}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; RPOW_EQ_0] THEN
    SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  ABBREV_TAC `EA = expectation p (\x. abs((f:A->real) x) rpow a)` THEN
  ABBREV_TAC `EB = expectation p (\x. abs((g:A->real) x) rpow b)` THEN
  SUBGOAL_THEN `&0 <= EA /\ &0 <= EB` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["EA"; "EB"] THEN CONJ_TAC THEN
    MATCH_MP_TAC EXPECTATION_POS THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inv a = &0) /\ ~(inv b = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_CASES_TAC `EA = &0` THENL
   [ASM_REWRITE_TAC[RPOW_ZERO; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `EB = &0` THENL
   [ASM_REWRITE_TAC[RPOW_ZERO; REAL_MUL_RZERO] THEN
    SUBGOAL_THEN `(\x. abs((f:A->real) x) * abs((g:A->real) x)) =
                  (\x. abs(g x) * abs(f x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < EA /\ &0 < EB` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(EA rpow inv a) rpow a = EA /\ (EB rpow inv b) rpow b = EB`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_LINV; REAL_LT_IMP_NZ; RPOW_POW;
                 REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y u v. &0 <= x /\ &0 <= y /\ &0 < u /\ &0 < v
              ==> x * y <= u * v * (inv a * inv(u rpow a) * x rpow a +
                                    inv b * inv(v rpow b) * y rpow b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(x:real) / u`; `(y:real) / v`; `a:real`; `b:real`]
           YOUNG_INEQUALITY) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; RPOW_DIV] THEN
    SUBGOAL_THEN `&0 < u rpow a /\ &0 < v rpow b` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real) * y = (u * v) * ((x * inv u) * y * inv v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_RING
       `(u:real) * inv u = &1 /\ v * inv v = &1
        ==> x * y = (u * v) * ((x * inv u) * y * inv v)`) THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `expectation p (\x. EA rpow inv a * EB rpow inv b *
                       (inv a * inv EA * abs((f:A->real) x) rpow a +
                        inv b * inv EB * abs((g:A->real) x) rpow b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT((MATCH_MP_TAC INTEGRABLE_CMUL) ORELSE
             (MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC)) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`abs((f:A->real) x)`; `abs((g:A->real) x)`; `EA rpow inv a`;
        `EB rpow inv b`]) THEN
      ASM_SIMP_TAC[REAL_ABS_POS; RPOW_POS_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integrable p (\x. inv EA * abs((f:A->real) x) rpow a) /\
    integrable p (\x. inv a * inv EA * abs(f x) rpow a) /\
    integrable p (\x. inv EB * abs((g:A->real) x) rpow b) /\
    integrable p (\x. inv b * inv EB * abs(g x) rpow b) /\
    integrable p (\x. inv a * inv EA * abs(f x) rpow a +
                      inv b * inv EB * abs(g x) rpow b) /\
    integrable p (\x. EB rpow inv b * (inv a * inv EA * abs(f x) rpow a +
                                       inv b * inv EB * abs(g x) rpow b))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC INTEGRABLE_CMUL) ORELSE
           (MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_CMUL; EXPECTATION_ADD] THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let EXPECTATION_LYAPUNOV = prove
 (`!p:A prob_space f r s.
        &0 < r /\ r <= s /\ integrable p (\x. abs(f x) rpow s)
        ==> integrable p (\x. abs(f x) rpow r) /\
            expectation p (\x. abs(f x) rpow r) rpow inv r <=
            expectation p (\x. abs(f x) rpow s) rpow inv s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (\x. abs((f:A->real) x) rpow r)` ASSUME_TAC
  THENL
   [SUBGOAL_THEN `(\x. abs((f:A->real) x) rpow r) =
                  (\x. (\y. y rpow (r / s)) (abs(f x) rpow s))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
      SIMP_TAC[RPOW_RPOW; REAL_ABS_POS] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. abs((f:A->real) x) rpow r)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x. &1 + abs((f:A->real) x) rpow s` THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CONST] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SIMP_TAC[REAL_ABS_RPOW; REAL_ABS_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= b /\ (a <= &1 \/ a <= b) ==> a <= abs(&1 + b)`) THEN
    SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN
    DISJ_CASES_TAC(REAL_ARITH `abs((f:A->real) x) <= &1 \/ &1 <= abs(f x)`)
    THENL
     [DISJ1_TAC THEN MATCH_MP_TAC RPOW_1_LE THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
      DISJ2_TAC THEN MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `r:real = s` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `r < s:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * s / r = s /\ inv(s / r) = r / s /\
                inv(s / (s - r)) = (s - r) / s /\ r / s + (s - r) / s = &1 /\
                &0 < s / r /\ &0 < s / (s - r) /\ r / s * inv r = inv s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_DIV] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. abs((f:A->real) x) rpow r`; `\x:A. &1`;
                 `(s:real) / r`; `(s:real) / (s - r)`]
         EXPECTATION_HOELDER) THEN
  ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; REAL_ABS_RPOW; REAL_ABS_ABS;
               REAL_ABS_NUM; RPOW_ONE; INTEGRABLE_CONST; RPOW_RPOW;
               REAL_ABS_POS;
               REAL_MUL_RID; EXPECTATION_CONST] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= expectation p (\x. abs((f:A->real) x) rpow r) /\
                &0 <= expectation p (\x. abs(f x) rpow s)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC EXPECTATION_POS THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `expectation p (\x. abs((f:A->real) x) rpow s) rpow inv s =
    (expectation p (\x. abs(f x) rpow s) rpow (r / s)) rpow inv r`
  SUBST1_TAC THENL [ASM_SIMP_TAC[RPOW_RPOW]; ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let EXPECTATION_LYAPUNOV_THREE = prove
 (`!p:A prob_space f r s t.
        &0 < r /\ r <= s /\ s <= t /\ integrable p (\x. abs(f x) rpow t)
        ==> expectation p (\x. abs(f x) rpow s) rpow (t - r) <=
            expectation p (\x. abs(f x) rpow r) rpow (t - s) *
            expectation p (\x. abs(f x) rpow t) rpow (s - r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. &0 < u /\ u <= t ==> integrable p (\x. abs((f:A->real) x) rpow u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `f:A->real`; `u:real`; `t:real`]
           EXPECTATION_LYAPUNOV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Er = expectation p (\x. abs((f:A->real) x) rpow r)` THEN
  ABBREV_TAC `Es = expectation p (\x. abs((f:A->real) x) rpow s)` THEN
  ABBREV_TAC `Et = expectation p (\x. abs((f:A->real) x) rpow t)` THEN
  SUBGOAL_THEN `&0 <= Er /\ &0 <= Es /\ &0 <= Et` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Er"; "Es"; "Et"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC EXPECTATION_POS THEN
    SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r:real = s` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `expectation p (\x. abs((f:A->real) x) rpow r) = Es` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[REAL_SUB_REFL; RPOW_0; REAL_MUL_RID; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `expectation p (\x. abs((f:A->real) x) rpow s) = Et` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[REAL_SUB_REFL; RPOW_0; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `r < s /\ s < t:real` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t - s /\ &0 < s - r /\ &0 < t - r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (t - s) / (t - r) /\ &0 < (s - r) / (t - r) /\
                (t - s) / (t - r) <= &1 /\ (s - r) / (t - r) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(t - s) / (t - r) + (s - r) / (t - r) = &1 /\
    (r * (t - s) / (t - r)) * inv((t - s) / (t - r)) = r /\
    (t * (s - r) / (t - r)) * inv((s - r) / (t - r)) = t /\
    (t - s) / (t - r) * (t - r) = t - s /\
    (s - r) / (t - r) * (t - r) = s - r /\
    r * (t - s) / (t - r) + t * (s - r) / (t - r) = s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < t - r` THEN UNDISCH_TAC `&0 < t - s` THEN
    UNDISCH_TAC `&0 < s - r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  SPEC_TAC(`((t:real) - s) / (t - r)`, `l:real`) THEN
  SPEC_TAC(`((s:real) - r) / (t - r)`, `m:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r * l /\ r * l <= t /\ &0 < t * m /\ t * m <= t`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= r * m /\ &0 <= t * l` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:real) * l = r - r * m /\ (t:real) * m = t - t * l`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(l:real) + m = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. abs(abs((f:A->real) x) rpow (r * l) * abs(f x) rpow (t * m))) =
    (\x. abs(f x) rpow s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; REAL_ABS_MUL; REAL_ABS_RPOW; REAL_ABS_ABS] THEN
    X_GEN_TAC `x:A` THEN
    MP_TAC(ISPECL [`abs((f:A->real) x)`; `(r:real) * l`; `(t:real) * m`]
           RPOW_ADD_ALT) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. abs((f:A->real) x) rpow (r * l)`;
                 `\x. abs((f:A->real) x) rpow (t * m)`; `inv l:real`;
                 `inv m:real`] EXPECTATION_HOELDER) THEN
  ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE; REAL_LT_INV_EQ; REAL_INV_INV;
               REAL_ABS_RPOW; REAL_ABS_ABS; RPOW_RPOW; REAL_ABS_POS;
               REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(Er rpow l * Et rpow m) rpow (t - r)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Chebyshev's association inequality: E[f] E[g] <= E[fg] when f and g are   *)
(* similarly ordered outside a null event.                                   *)
(* ------------------------------------------------------------------------- *)

let EXPECTATION_SIMILARLY_ORDERED_GE = prove
 (`!p:A prob_space f g n.
        integrable p f /\ integrable p g /\ integrable p (\x. f x * g x) /\
        null_event p n /\
        (!x y. x IN prob_carrier p /\ y IN prob_carrier p /\
               ~(x IN n) /\ ~(y IN n)
               ==> &0 <= (f x - f y) * (g x - g y))
        ==> expectation p f * expectation p g <=
            expectation p (\x. f x * g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!P. (!x:A. x IN prob_carrier p /\ ~(x IN n) ==> P x)
                    ==> almost_surely p {x | P x}` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[almost_surely] THEN
    EXISTS_TAC `n:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a < &0 /\ &0 <= a * b ==> b <= &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`--a:real`; `b:real`] REAL_LT_MUL) THEN
    ASM_REWRITE_TAC[REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = expectation p (f:A->real)` THEN
  SUBGOAL_THEN `?c. almost_surely p {x:A | &0 <= (f x - m) * (g x - c)}`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC
     `(?x:A. x IN prob_carrier p /\ ~(x IN n) /\ (f:A->real) x < m) /\
      (?y:A. y IN prob_carrier p /\ ~(y IN n) /\ m < f y)` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC)) THEN
      ABBREV_TAC
       `S = {(g:A->real) x | x IN prob_carrier p /\ ~(x IN n) /\
                             (f:A->real) x < m}` THEN
      MP_TAC(SPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
       [EXPAND_TAC "S" THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `(g:A->real) y0` THEN X_GEN_TAC `z:real` THEN
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
        REWRITE_TAC[REAL_ARITH `&0 <= a - b <=> b - a <= &0`] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(f:A->real) x - f y0` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
        STRIP_TAC] THEN
      EXISTS_TAC `sup S` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (REAL_ARITH `(f:A->real) x < m \/ f x = m \/ m < f x`) THENL
       [SUBGOAL_THEN `(g:A->real) x <= sup S` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
          DISCH_TAC] THEN
        ONCE_REWRITE_TAC[REAL_RING
         `((a:real) - b) * (c - d) = (b - a) * (d - c)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_LE_REFL];
        SUBGOAL_THEN `sup S <= (g:A->real) x` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real` THEN
          DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
          REWRITE_TAC[REAL_ARITH `&0 <= a - b <=> b - a <= &0`] THEN
          FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(f:A->real) w - f x` THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
          DISCH_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `&0` THEN
    SUBGOAL_THEN `almost_surely p {x:A | (f:A->real) x - m = &0}` MP_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM;
        NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`;
        REAL_NOT_LT]) THENL
       [MP_TAC(ISPECL [`p:A prob_space`; `\x. (f:A->real) x - m`]
               EXPECTATION_AS_NONNEG_ZERO) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_SUB_LE];
          ASM_SIMP_TAC[EXPECTATION_SUB_CONST; REAL_SUB_REFL]];
        MP_TAC(ISPECL [`p:A prob_space`; `\x. m - (f:A->real) x`]
               EXPECTATION_AS_NONNEG_ZERO) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC INTEGRABLE_SUB THEN
            ASM_REWRITE_TAC[INTEGRABLE_CONST];
            FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_SUB_LE];
            ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_CONST; EXPECTATION_CONST;
                         REAL_SUB_REFL]];
          DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
          EXISTS_TAC `{x:A | m - (f:A->real) x = &0}` THEN
          ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]];
      DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x:A | (f:A->real) x - m = &0}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_LZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integrable p (\x. c * (f:A->real) x) /\
    integrable p (\x. m * (g:A->real) x) /\
    integrable p (\x. f x * g x - c * f x) /\
    integrable p (\x. (f x * g x - c * f x) - m * g x) /\
    integrable p (\x. ((f x * g x - c * f x) - m * g x) + m * c)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC) ORELSE
           MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. &0`;
                 `\x. (((f:A->real) x * g x - c * f x) - m * g x) + m * c`]
         EXPECTATION_MONO_AE) THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | &0 <= ((f:A->real) x - m) * (g x - c)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(((f:A->real) x * g x - c * f x) - m * g x) + m * c =
                  (f x - m) * (g x - c)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; REWRITE_TAC[]];
    ASM_SIMP_TAC[EXPECTATION_ADD; EXPECTATION_SUB; EXPECTATION_CMUL;
                 EXPECTATION_CONST; INTEGRABLE_CONST] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bonferroni's inequalities, pointwise: the truncated inclusion-exclusion   *)
(* sums alternate around the indicator of a finite union.                    *)
(* ------------------------------------------------------------------------- *)

let SUM_ALTERNATING_BINOM_PARTIAL = prove
 (`!N k. sum(0..k) (\j. (-- &1) pow j * &(binom(N + 1,j))) =
         (-- &1) pow k * &(binom(N,k))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; binom; real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM ADD1; binom; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let SUM_INDICATOR_INTERS_SUBSETS = prove
 (`!(A:K->B->bool) s x j.
        FINITE s
        ==> sum {t | t SUBSET s /\ CARD t = j}
                (\t. indicator_fn (INTERS (IMAGE A t)) x) =
            &(binom(CARD {i | i IN s /\ x IN A i},j))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = {i | i IN s /\ (x:B) IN (A:K->B->bool) i}` THEN
  SUBGOAL_THEN `FINITE (u:K->bool) /\ u SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[FINITE_RESTRICT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum {t | t SUBSET s /\ CARD t = j}
        (\t:K->bool. if t SUBSET u then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:K->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[indicator_fn; IN_INTERS; FORALL_IN_IMAGE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_SUBSETS_RESTRICT;
               REAL_MUL_RID] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM CARD_RESTRICTED_POWERSET] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; HAS_SIZE] THEN
  ASM_MESON_TAC[SUBSET_TRANS; FINITE_SUBSET]);;

let BONFERRONI_INDICATOR = prove
 (`!(A:K->B->bool) s k x.
        FINITE s
        ==> (ODD k ==> indicator_fn (UNIONS (IMAGE A s)) x <=
                       sum(1..k) (\j. (-- &1) pow (j + 1) *
                          sum {t | t SUBSET s /\ CARD t = j}
                              (\t. indicator_fn (INTERS (IMAGE A t)) x))) /\
            (EVEN k ==> sum(1..k) (\j. (-- &1) pow (j + 1) *
                          sum {t | t SUBSET s /\ CARD t = j}
                              (\t. indicator_fn (INTERS (IMAGE A t)) x))
                        <= indicator_fn (UNIONS (IMAGE A s)) x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SUM_INDICATOR_INTERS_SUBSETS] THEN
  SUBGOAL_THEN `indicator_fn (UNIONS (IMAGE (A:K->B->bool) s)) x =
                if CARD {i | i IN s /\ x IN A i} = 0 then &0 else &1`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT] THEN
    REWRITE_TAC[indicator_fn; IN_UNIONS; EXISTS_IN_IMAGE; EXTENSION;
                IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EXISTS_THM] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = CARD {i | i IN s /\ (x:B) IN (A:K->B->bool) i}` THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `sum(1..k) (\j. (-- &1) pow (j + 1) * &(binom(0,j))) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `binom(0,i) = 0` SUBST1_TAC THENL
       [REWRITE_TAC[BINOM_EQ_0] THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO]];
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
    (ARITH_RULE `~(m = 0) ==> m = (m - 1) + 1`)) THEN
  ABBREV_TAC `N = m - 1` THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `sum(1..k) (\j. (-- &1) pow (j + 1) * &(binom(N + 1,j))) =
                &1 - (-- &1) pow k * &(binom(N,k))` SUBST1_TAC THENL
   [MP_TAC(SPECL [`N:num`; `k:num`] SUM_ALTERNATING_BINOM_PARTIAL) THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
    REWRITE_TAC[binom; real_pow; REAL_MUL_LID; REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `(a * -- &1) * b = --(a * b)`; SUM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `binom(N,k)` REAL_POS) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The sheet's inequalities. Chebyshev 1 is the library's                    *)
(* CHEBYSHEV_INEQUALITY.                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Jensen's inequality for expectation, for f convex (or concave) on a real  *)
(* interval holding X almost surely; Chebyshev's inequality for f(X), g(X)   *)
(* with f, g nondecreasing on a set holding X almost surely.                 *)
(* ------------------------------------------------------------------------- *)

let JENSEN_EXPECTATION = prove
 (`!p:A prob_space X f s.
        is_realinterval s /\ f real_convex_on s /\
        almost_surely p {x | X x IN s} /\
        integrable p X /\ integrable p (\x. f(X x))
        ==> f(expectation p X) <= expectation p (\x. f(X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `s:real->bool`]
         EXPECTATION_IN_REALINTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = expectation p (X:A->real)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `almost_surely p {x:A | (X:A->real) x = m} \/
    ?c. !y. y IN s ==> f m + c * (y - m) <= (f:real->real) y`
  MP_TAC THENL
   [ASM_CASES_TAC `(?a. a IN s /\ a < m) /\ (?b. b IN s /\ m < b:real)` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC REAL_CONVEX_ON_SUPPORTING_LINE THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(a /\ b) <=> a ==> ~b`; REAL_NOT_LT]) THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `\x. (X:A->real) x - m`]
             EXPECTATION_AS_NONNEG_ZERO) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
          MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
          EXISTS_TAC `{x:A | (X:A->real) x IN s}` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_SUB_LE];
          ASM_SIMP_TAC[EXPECTATION_SUB_CONST; REAL_SUB_REFL]];
        DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
        EXISTS_TAC `{x:A | (X:A->real) x - m = &0}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL [`p:A prob_space`; `\x. m - (X:A->real) x`]
             EXPECTATION_AS_NONNEG_ZERO) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
          MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
          EXISTS_TAC `{x:A | (X:A->real) x IN s}` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_SUB_LE];
          ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_CONST; EXPECTATION_CONST;
                       REAL_SUB_REFL]];
        DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
        EXISTS_TAC `{x:A | m - (X:A->real) x = &0}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. (f:real->real) m`;
                   `\x. (f:real->real)((X:A->real) x)`] EXPECTATION_AS_EQ) THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; INTEGRABLE_IMP_RANDOM_VARIABLE;
                 EXPECTATION_CONST] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x:A | (X:A->real) x = m}` THEN ASM_SIMP_TAC[IN_ELIM_THM];
      SIMP_TAC[REAL_LE_REFL]];
    SUBGOAL_THEN `integrable p (\x:A. (f:real->real) m + c * (X x - m))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ADD THEN REWRITE_TAC[INTEGRABLE_CONST] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `\x:A. (f:real->real) m + c * (X x - m)`;
                   `\x. (f:real->real)((X:A->real) x)`]
           EXPECTATION_MONO_AE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x:A | (X:A->real) x IN s}` THEN ASM_SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `integrable p (\x:A. c * ((X:A->real) x - m)) /\
                  integrable p (\x:A. (X:A->real) x - m)` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL ORELSE
             MATCH_MP_TAC INTEGRABLE_SUB) THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EXPECTATION_ADD; EXPECTATION_CMUL; EXPECTATION_SUB_CONST;
                 INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID]]);;

let JENSEN_EXPECTATION_CONCAVE = prove
 (`!p:A prob_space X f s.
        is_realinterval s /\ (\y. --(f y)) real_convex_on s /\
        almost_surely p {x | X x IN s} /\
        integrable p X /\ integrable p (\x. f(X x))
        ==> expectation p (\x. f(X x)) <= f(expectation p X)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `\y. --((f:real->real) y)`;
                 `s:real->bool`] JENSEN_EXPECTATION) THEN
  ASM_SIMP_TAC[INTEGRABLE_NEG; EXPECTATION_NEG_INTEGRABLE] THEN
  REAL_ARITH_TAC);;

let CHEBYSHEV_EXPECTATION_INEQUALITY = prove
 (`!p:A prob_space X f g s:real->bool.
        almost_surely p {x | X x IN s} /\
        (!u v. u IN s /\ v IN s /\ u <= v ==> f u <= f v /\ g u <= g v) /\
        integrable p (\x. f(X x)) /\ integrable p (\x. g(X x)) /\
        integrable p (\x. f(X x) * g(X x))
        ==> expectation p (\x. f(X x)) * expectation p (\x. g(X x)) <=
            expectation p (\x. f(X x) * g(X x))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC o
                GEN_REWRITE_RULE I [almost_surely]) THEN
  MATCH_MP_TAC EXPECTATION_SIMILARLY_ORDERED_GE THEN
  EXISTS_TAC `n:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X:A->real) x IN s /\ X y IN s` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`(X:A->real) x`; `(X:A->real) y`] REAL_LE_TOTAL)
  THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`(X:A->real) x`; `(X:A->real) y`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_RING
     `((a:real) - b) * (c - d) = (b - a) * (d - c)`];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(X:A->real) y`; `(X:A->real) x`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Markov's inequality and its variants (Markov 1-3).                        *)
(* ------------------------------------------------------------------------- *)

let MARKOV_ABS_INEQUALITY = prove
 (`!p:A prob_space X a.
        integrable p X /\ &0 < a
        ==> prob p {x | x IN prob_carrier p /\ abs(X x) >= a} <=
            expectation p (\x. abs(X x)) / a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC MARKOV_EVENT_INEQUALITY THEN
  ASM_SIMP_TAC[INTEGRABLE_ABS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; REAL_ABS_POS];
    MATCH_MP_TAC RV_PREIMAGE_GE THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE];
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; real_ge] THEN
    MESON_TAC[]]);;

let MARKOV_UPPER_INEQUALITY_GEN = prove
 (`!p:A prob_space X b c.
        integrable p X /\ almost_surely p {x | X x <= b} /\ c < b
        ==> prob p {x | x IN prob_carrier p /\ X x <= c} <=
            (b - expectation p X) / (b - c)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. b - (X:A->real) x`;
                 `{x | x IN prob_carrier p /\ (X:A->real) x <= c}`;
                 `b - c:real`] MARKOV_EVENT_INEQUALITY) THEN
  ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_SUB; INTEGRABLE_CONST;
               EXPECTATION_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | (X:A->real) x <= b}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC RV_PREIMAGE_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE];
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let MARKOV_UPPER_INEQUALITY = prove
 (`!p:A prob_space X c.
        integrable p X /\ almost_surely p {x | X x <= &1} /\ c < &1
        ==> prob p {x | x IN prob_carrier p /\ X x <= c} <=
            (&1 - expectation p X) / (&1 - c)`,
  SIMP_TAC[MARKOV_UPPER_INEQUALITY_GEN]);;

let MARKOV_SET_INEQUALITY = prove
 (`!p:A prob_space (X:A->B) (f:B->real) (S:B->bool) s.
        integrable p (\x. f(X x)) /\ almost_surely p {x | &0 <= f(X x)} /\
        &0 < s /\ (!y. y IN S ==> s <= f y) /\
        {x | x IN prob_carrier p /\ X x IN S} IN prob_events p
        ==> prob p {x | x IN prob_carrier p /\ X x IN S} <=
            expectation p (\x. f(X x)) / s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC MARKOV_EVENT_INEQUALITY THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
  REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Moment inequalities: the k-th central moment for even k, and any real     *)
(* moment k > 0 about any centre.                                            *)
(* ------------------------------------------------------------------------- *)

let KTH_MOMENT_INEQUALITY = prove
 (`!p:A prob_space X k t.
        EVEN k /\ integrable p X /\
        integrable p (\x. (X x - expectation p X) pow k) /\ &0 < t
        ==> prob p {x | x IN prob_carrier p /\
                        abs(X x - expectation p X) >= t} <=
            expectation p (\x. (X x - expectation p X) pow k) / t pow k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = expectation p (X:A->real)` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC MARKOV_EVENT_INEQUALITY THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(X:A->real) x - m`; `k:num`] REAL_EVENPOW_ABS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[REAL_POW_LE; REAL_ABS_POS];
    MATCH_MP_TAC RV_PREIMAGE_GE THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; INTEGRABLE_IMP_RANDOM_VARIABLE];
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; real_ge] THEN
    X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`(X:A->real) x - m`; `k:num`] REAL_EVENPOW_ABS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let KTH_MOMENT_INEQUALITY_GEN = prove
 (`!p:A prob_space X mu k t.
        &0 < k /\ &0 < t /\ integrable p (\x. abs(X x - mu) rpow k)
        ==> prob p {x | x IN prob_carrier p /\ abs(X x - mu) >= t} <=
            expectation p (\x. abs(X x - mu) rpow k) / t rpow k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; RPOW_POS_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ abs((X:A->real) x - mu) >= t} =
    {x | x IN prob_carrier p /\ abs(X x - mu) rpow k >= t rpow k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge] THEN X_GEN_TAC `x:A` THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN MATCH_MP_TAC RPOW_LT2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC MARKOV_EVENT_INEQUALITY THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    SIMP_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; RPOW_POS_LE; REAL_ABS_POS];
    MATCH_MP_TAC RV_PREIMAGE_GE THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE];
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; real_ge] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The second moment method (2nd moment 1 and 2), as products and in the     *)
(* sheet's quotient form.                                                    *)
(* ------------------------------------------------------------------------- *)

let SECOND_MOMENT_POS_INEQUALITY = prove
 (`!p:A prob_space X.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        &0 <= expectation p X
        ==> expectation p X pow 2 <=
            expectation p (\x. X x pow 2) *
            prob p {x | x IN prob_carrier p /\ X x > &0}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {x | x IN prob_carrier p /\ (X:A->real) x > &0}` THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC RV_PREIMAGE_GT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `expectation p (\x. (X:A->real) x * indicator_fn A x) pow 2` THEN
  ASM_SIMP_TAC[EXPECTATION_CAUCHY_SCHWARZ_EVENT] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EXPECTATION_MONO THEN
  ASM_SIMP_TAC[INTEGRABLE_POW2_IMP; INTEGRABLE_MUL_INDICATOR_FN] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
  REWRITE_TAC[indicator_fn; IN_ELIM_THM; real_gt] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let SECOND_MOMENT_POS_INEQUALITY_DIV = prove
 (`!p:A prob_space X.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        &0 <= expectation p X
        ==> expectation p X pow 2 / expectation p (\x. X x pow 2) <=
            prob p {x | x IN prob_carrier p /\ X x > &0}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ (X:A->real) x > &0} IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= expectation p (\x. (X:A->real) x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC SECOND_MOMENT_POS_INEQUALITY THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]]);;

let SECOND_MOMENT_ZERO_INEQUALITY = prove
 (`!p:A prob_space X.
        random_variable p X /\ integrable p (\x. X x pow 2)
        ==> expectation p (\x. X x pow 2) *
            prob p {x | x IN prob_carrier p /\ X x = &0}
            <= variance p X`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Z = {x | x IN prob_carrier p /\ (X:A->real) x = &0}` THEN
  SUBGOAL_THEN `(Z:A->bool) IN prob_events p` ASSUME_TAC THENL
   [SUBGOAL_THEN `Z = {x | x IN prob_carrier p /\ abs((X:A->real) x) <= &0}`
    SUBST1_TAC THENL
     [EXPAND_TAC "Z" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM;
                  REAL_ARITH `abs(x:real) <= &0 <=> x = &0`];
      MATCH_MP_TAC RV_PREIMAGE_LE THEN MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`;
                 `prob_carrier p DIFF (Z:A->bool)`]
         EXPECTATION_CAUCHY_SCHWARZ_EVENT) THEN
  ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; PROB_COMPL] THEN
  SUBGOAL_THEN
   `expectation p
      (\x. (X:A->real) x * indicator_fn (prob_carrier p DIFF Z) x) =
    expectation p X`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EXPECTATION_EXT THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    EXPAND_TAC "Z" THEN REWRITE_TAC[indicator_fn; IN_DIFF; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VARIANCE_ALT; INTEGRABLE_POW2_IMP] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC);;

let SECOND_MOMENT_ZERO_INEQUALITY_DIV = prove
 (`!p:A prob_space X.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        ~(expectation p (\x. X x pow 2) = &0)
        ==> prob p {x | x IN prob_carrier p /\ X x = &0} <=
            variance p X / expectation p (\x. X x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < expectation p (\x. (X:A->real) x pow 2)` ASSUME_TAC
  THENL
   [ASM_REWRITE_TAC[REAL_LT_LE] THEN MATCH_MP_TAC EXPECTATION_POS THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC SECOND_MOMENT_ZERO_INEQUALITY THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Bhatia-Davis inequality.                                              *)
(* ------------------------------------------------------------------------- *)

let BHATIA_DAVIS_INEQUALITY = prove
 (`!p:A prob_space X m M.
        random_variable p X /\ almost_surely p {x | m <= X x /\ X x <= M}
        ==> variance p X <= (M - expectation p X) * (expectation p X - m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real) /\ integrable p (\x. X x pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THENL
     [EXISTS_TAC `abs(m:real) + abs(M:real)`;
      EXISTS_TAC `(abs(m:real) + abs(M:real)) pow 2`] THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_POW] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | m <= (X:A->real) x /\ X x <= M}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `mu = expectation p (X:A->real)` THEN
  ABBREV_TAC `EX2 = expectation p (\x. (X:A->real) x pow 2)` THEN
  SUBGOAL_THEN
   `&0 <= expectation p (\x. (M + m) * (X:A->real) x - X x pow 2 - M * m)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `integrable p (\x. (M + m) * (X:A->real) x - X x pow 2 - M * m)`
    ASSUME_TAC THENL
     [REPEAT((MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC) ORELSE
             MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `\x:A. &0`;
                   `\x. (M + m) * (X:A->real) x - X x pow 2 - M * m`]
           EXPECTATION_MONO_AE) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x:A | m <= (X:A->real) x /\ X x <= M}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(M + m) * (X:A->real) x - X x pow 2 - M * m =
                  (M - X x) * (X x - m)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. (M + m) * (X:A->real) x) /\
                integrable p (\x. (M + m) * (X:A->real) x - X x pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC) ORELSE
           MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_SUB_CONST; EXPECTATION_SUB; EXPECTATION_CMUL] THEN
  ASM_SIMP_TAC[VARIANCE_ALT] THEN
  SUBGOAL_THEN `((M:real) - mu) * (mu - m) - (EX2 - mu pow 2) =
                (M + m) * mu - EX2 - M * m` MP_TAC THENL
   [CONV_TAC REAL_RING; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Cantelli's inequality (Chebyshev 2), for both tails.                      *)
(* ------------------------------------------------------------------------- *)

let CANTELLI_INEQUALITY = prove
 (`!p:A prob_space X t.
        random_variable p X /\ integrable p (\x. X x pow 2) /\ &0 < t
        ==> prob p {x | x IN prob_carrier p /\ X x - expectation p X >= t} <=
            variance p X / (variance p X + t pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_POW2_IMP]; ALL_TAC] THEN
  ABBREV_TAC `mu = expectation p (X:A->real)` THEN
  SUBGOAL_THEN
   `!a b c. integrable p (\x. a * (X:A->real) x pow 2 + b * X x + c)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE
           MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b c. expectation p (\x. a * (X:A->real) x pow 2 + b * X x + c) =
            a * expectation p (\x. X x pow 2) + b * mu + c`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `integrable p (\x. a * (X:A->real) x pow 2) /\
                  integrable p (\x. b * (X:A->real) x) /\
                  integrable p (\x. b * (X:A->real) x + c)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE
             MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      ASM_SIMP_TAC[EXPECTATION_ADD; EXPECTATION_CMUL; INTEGRABLE_CONST;
                   EXPECTATION_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `variance p (X:A->real) = expectation p (\x. X x pow 2) - mu pow 2`
  ASSUME_TAC THENL [ASM_SIMP_TAC[VARIANCE_ALT]; ALL_TAC] THEN
  ABBREV_TAC `EX2 = expectation p (\x. (X:A->real) x pow 2)` THEN
  ABBREV_TAC `V = variance p (X:A->real)` THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`;
                   `\x. &1 * (X:A->real) x pow 2 + (-- &2 * mu) * X x +
                        mu pow 2`] EXPECTATION_POS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&1 * (X:A->real) x pow 2 + (-- &2 * mu) * X x +
                    mu pow 2 = (X x - mu) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; REWRITE_TAC[REAL_LE_POW_2]];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (V:real) / t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `u = (V:real) / t` THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                 `\x. &1 * (X:A->real) x pow 2 + (&2 * (u - mu)) * X x +
                      (u - mu) pow 2`;
                 `{x | x IN prob_carrier p /\ (X:A->real) x - mu >= t}`;
                 `((t:real) + u) pow 2`] MARKOV_EVENT_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&1 * (X:A->real) x pow 2 + (&2 * (u - mu)) * X x +
                    (u - mu) pow 2 = (X x + (u - mu)) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RING; REWRITE_TAC[REAL_LE_POW_2]];
      MATCH_MP_TAC RV_PREIMAGE_GE THEN MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
      ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; real_ge] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&1 * (X:A->real) x pow 2 + (&2 * (u - mu)) * X x +
                    (u - mu) pow 2 = (X x + (u - mu)) pow 2` SUBST1_TAC THENL
       [CONV_TAC REAL_RING;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `EX2 = (V:real) + mu pow 2`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `((V:real) + m) - m = V`] THEN
  ABBREV_TAC
   `P = prob p {x | x IN prob_carrier p /\ (X:A->real) x - mu >= t}` THEN
  SUBGOAL_THEN `u * t = V:real` ASSUME_TAC THENL
   [UNDISCH_TAC `(V:real) / t = u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow 2 + V` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ;
               REAL_ARITH `(V:real) + t pow 2 = t pow 2 + V`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_LE_LMUL_EQ) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN
   `((t:real) pow 2 + V) * (P * (t pow 2 + V)) =
    ((t + u) pow 2 * P) * t pow 2 /\
    ((t:real) pow 2 + V) * V =
    (&1 * (V + mu pow 2) + (&2 * (u - mu)) * mu + (u - mu) pow 2) * t pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `u * t = V:real` THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

let CANTELLI_INEQUALITY_NEG = prove
 (`!p:A prob_space X t.
        random_variable p X /\ integrable p (\x. X x pow 2) /\ &0 < t
        ==> prob p {x | x IN prob_carrier p /\ X x - expectation p X <= --t} <=
            variance p X / (variance p X + t pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. --((X:A->real) x)`; `t:real`]
         CANTELLI_INEQUALITY) THEN
  ASM_SIMP_TAC[RANDOM_VARIABLE_NEG; REAL_POW_NEG; ARITH; VARIANCE_NEG;
               EXPECTATION_NEG_INTEGRABLE; INTEGRABLE_POW2_IMP] THEN
  REWRITE_TAC[REAL_ARITH `--(a:real) - --b >= t <=> a - b <= --t`]);;

(* ------------------------------------------------------------------------- *)
(* The fourth moment inequality, as a product and in the sheet's form.       *)
(* ------------------------------------------------------------------------- *)

let FOURTH_MOMENT_INEQUALITY = prove
 (`!p:A prob_space X.
        integrable p (\x. X x pow 4)
        ==> expectation p (\x. X x pow 2) pow 3 <=
            expectation p (\x. abs(X x)) pow 2 *
            expectation p (\x. X x pow 4)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&1`; `&2`; `&4`]
         EXPECTATION_LYAPUNOV_THREE) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_POW2_ABS] THEN
  SIMP_TAC[REAL_EVENPOW_ABS; ARITH] THEN ASM_REWRITE_TAC[]);;

let FOURTH_MOMENT_INEQUALITY_DIV = prove
 (`!p:A prob_space X.
        integrable p (\x. X x pow 4)
        ==> expectation p (\x. X x pow 2) rpow (&3 / &2) /
            sqrt(expectation p (\x. X x pow 4)) <=
            expectation p (\x. abs(X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL FOURTH_MOMENT_INEQUALITY) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `integrable p (\x. (X:A->real) x pow 2) /\
                integrable p (\x. abs((X:A->real) x))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&2`; `&4`]
             EXPECTATION_LYAPUNOV);
      MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&1`; `&4`]
             EXPECTATION_LYAPUNOV)] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_POW2_ABS] THEN
    SIMP_TAC[REAL_EVENPOW_ABS; ARITH] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = expectation p (\x. (X:A->real) x pow 2)` THEN
  ABBREV_TAC `b = expectation p (\x. abs((X:A->real) x))` THEN
  ABBREV_TAC `c = expectation p (\x. (X:A->real) x pow 4)` THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b /\ &0 <= c` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS] THEN
    REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[SQRT_0; real_div; REAL_INV_0; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; ARITH] THEN
  ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2] THEN
  SUBGOAL_THEN `(a rpow (&3 / &2)) pow 2 = a pow 3` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REFL_TAC;
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Paley-Zygmund inequality: for any exponent q > 1 (Hoelder form), the  *)
(* variance form, and the sheet's form with E[X^2].                          *)
(* ------------------------------------------------------------------------- *)

let PALEY_ZYGMUND_HOELDER = prove
 (`!p:A prob_space X d q.
        &1 < q /\ random_variable p X /\ integrable p (\x. abs(X x) rpow q) /\
        &0 <= expectation p X /\ d <= &1
        ==> ((&1 - d) * expectation p X) rpow (q / (q - &1)) <=
            expectation p (\x. abs(X x - d * expectation p X) rpow q)
              rpow inv(q - &1) *
            prob p {x | x IN prob_carrier p /\ X x > d * expectation p X}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x. abs((X:A->real) x) rpow &1` THEN
    ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_ABS_ABS; REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `&1`; `q:real`]
           EXPECTATION_LYAPUNOV) THEN
    ASM_SIMP_TAC[REAL_LT_01; REAL_LT_IMP_LE] THEN
    SIMP_TAC[RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  ABBREV_TAC `mu = expectation p (X:A->real)` THEN
  ABBREV_TAC `A = {x | x IN prob_carrier p /\ (X:A->real) x > d * mu}` THEN
  SUBGOAL_THEN `(A:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC RV_PREIMAGE_GT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q - &1 /\ &0 < q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < q / (q - &1) /\ inv q + inv(q / (q - &1)) = &1 /\
    inv(q / (q - &1)) = (q - &1) / q /\
    inv q * q / (q - &1) = inv(q - &1) /\
    (q - &1) / q * q / (q - &1) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_INV_DIV] THEN
    UNDISCH_TAC `&0 < q - &1` THEN UNDISCH_TAC `&0 < q` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a c. abs(a - c) rpow q <= &2 rpow q * (abs a rpow q + abs c rpow q)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    TRANS_TAC REAL_LE_TRANS `(&2 * max (abs a) (abs c)) rpow q` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC[RPOW_POS_LE; REAL_POS] THEN
      MP_TAC(SPECL [`abs(a:real)`; `q:real`] RPOW_POS_LE) THEN
      MP_TAC(SPECL [`abs(c:real)`; `q:real`] RPOW_POS_LE) THEN
      REWRITE_TAC[REAL_ABS_POS; real_max] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. abs((X:A->real) x - d * mu) rpow q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_DOMINATED THEN
    EXISTS_TAC `\x. &2 rpow q * (abs((X:A->real) x) rpow q +
                                 abs(d * mu) rpow q)` THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. abs((X:A->real) x - d * mu) rpow q) =
                    (\x. (\y. y rpow q) ((\x. abs(X x - d * mu)) x))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC RANDOM_VARIABLE_COMP_CONTINUOUS THEN CONJ_TAC THENL
       [MATCH_MP_TAC RANDOM_VARIABLE_ABS THEN
        MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
        ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= abs b`) THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. abs(indicator_fn (A:A->bool) x) rpow ((q:real) / (q - &1))) =
    indicator_fn A`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; indicator_fn] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM; RPOW_ONE; RPOW_ZERO] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x. (X:A->real) x - d * mu`;
                 `indicator_fn (A:A->bool)`; `q:real`; `(q:real) / (q - &1)`]
         EXPECTATION_HOELDER) THEN
  ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST;
               INTEGRABLE_INDICATOR; INTEGRABLE_IMP_RANDOM_VARIABLE;
               EXPECTATION_INDICATOR] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(&1 - d) * mu <=
    expectation p (\x. abs(((X:A->real) x - d * mu) * indicator_fn A x))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `expectation p (\x. ((X:A->real) x - d * mu) * indicator_fn A x)` THEN
    CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `expectation p (\x. (X:A->real) x - d * mu)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[EXPECTATION_SUB_CONST] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC EXPECTATION_MONO THEN
        ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CONST] THEN
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN
        REWRITE_TAC[indicator_fn; IN_ELIM_THM; real_gt] THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC EXPECTATION_MONO THEN
      ASM_SIMP_TAC[INTEGRABLE_ABS; REAL_ABS_LE]];
    ALL_TAC] THEN
  ABBREV_TAC
   `M = expectation p (\x. abs((X:A->real) x - d * mu) rpow q)` THEN
  SUBGOAL_THEN `&0 <= M /\ &0 <= prob (p:A prob_space) (A:A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC EXPECTATION_POS THEN
      ASM_SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS];
      MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `((M:real) rpow inv q *
     prob (p:A prob_space) (A:A->bool) rpow ((q - &1) / q))
    rpow (q / (q - &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; RPOW_POW; REAL_POW_1; REAL_LE_REFL]]);;

let PALEY_ZYGMUND_VARIANCE = prove
 (`!p:A prob_space X d.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        &0 <= expectation p X /\ d <= &1
        ==> (&1 - d) pow 2 * expectation p X pow 2 <=
            (variance p X + (&1 - d) pow 2 * expectation p X pow 2) *
            prob p {x | x IN prob_carrier p /\ X x > d * expectation p X}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `d:real`; `&2`]
         PALEY_ZYGMUND_HOELDER) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_POW2_ABS; REAL_POW_MUL] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_POW2_IMP]; ALL_TAC] THEN
  ABBREV_TAC `mu = expectation p (X:A->real)` THEN
  SUBGOAL_THEN
   `expectation p (\x. ((X:A->real) x - d * mu) pow 2) =
    variance p X + (&1 - d) pow 2 * mu pow 2`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[VARIANCE_ALT] THEN
    SUBGOAL_THEN
     `(\x. ((X:A->real) x - d * mu) pow 2) =
      (\x. &1 * X x pow 2 + (-- &2 * d * mu) * X x + (d * mu) pow 2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `integrable p (\x. &1 * (X:A->real) x pow 2) /\
                  integrable p (\x. (-- &2 * d * mu) * (X:A->real) x) /\
                  integrable p (\x. (-- &2 * d * mu) * (X:A->real) x +
                                    (d * mu) pow 2)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE
             MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST];
      ASM_SIMP_TAC[EXPECTATION_ADD; EXPECTATION_CMUL; INTEGRABLE_CONST;
                   EXPECTATION_CONST] THEN
      CONV_TAC REAL_RING];
    REWRITE_TAC[]]);;

let PALEY_ZYGMUND_INEQUALITY = prove
 (`!p:A prob_space X d.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        &0 <= expectation p X /\ &0 <= d /\ d <= &1
        ==> (&1 - d) pow 2 * expectation p X pow 2 <=
            expectation p (\x. X x pow 2) *
            prob p {x | x IN prob_carrier p /\ X x >= d * expectation p X}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:A->real`; `d:real`]
         PALEY_ZYGMUND_VARIANCE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_POW2_IMP]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= variance p (X:A->real)` MP_TAC THENL
   [MATCH_MP_TAC VARIANCE_NONNEG THEN
    SUBGOAL_THEN
     `(\x. ((X:A->real) x - expectation p X) pow 2) =
      (\x. &1 * X x pow 2 + (-- &2 * expectation p X) * X x +
           expectation p X pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC REAL_RING;
      REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE
             MATCH_MP_TAC INTEGRABLE_CMUL) THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[VARIANCE_ALT] THEN
  ABBREV_TAC `mu = expectation p (X:A->real)` THEN
  ABBREV_TAC `EX2 = expectation p (\x. (X:A->real) x pow 2)` THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ (X:A->real) x > d * mu} IN prob_events p /\
    {x | x IN prob_carrier p /\ (X:A->real) x >= d * mu} IN prob_events p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RV_PREIMAGE_GT; MATCH_MP_TAC RV_PREIMAGE_GE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                 `{x | x IN prob_carrier p /\ (X:A->real) x > d * mu}`;
                 `{x | x IN prob_carrier p /\ (X:A->real) x >= d * mu}`]
         PROB_MONO) THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  ANTS_TAC THENL [SIMP_TAC[real_gt; real_ge; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`;
                 `{x | x IN prob_carrier p /\ (X:A->real) x > d * mu}`]
         PROB_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - d) pow 2 * mu pow 2 <= mu pow 2` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `mu:real` REAL_LE_POW_2) THEN
  ABBREV_TAC
   `P1 = prob p {x | x IN prob_carrier p /\ (X:A->real) x > d * mu}` THEN
  ABBREV_TAC
   `P2 = prob p {x | x IN prob_carrier p /\ (X:A->real) x >= d * mu}` THEN
  REPEAT DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `((EX2:real) - mu pow 2 + (&1 - d) pow 2 * mu pow 2) * P1` THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS `(EX2:real) * P1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let PALEY_ZYGMUND_INEQUALITY_DIV = prove
 (`!p:A prob_space X d.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        &0 <= expectation p X /\ &0 <= d /\ d <= &1
        ==> (&1 - d) pow 2 * expectation p X pow 2 /
            expectation p (\x. X x pow 2) <=
            prob p {x | x IN prob_carrier p /\ X x >= d * expectation p X}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN prob_carrier p /\ (X:A->real) x >= d * expectation p X}
    IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 <= expectation p (\x. (X:A->real) x pow 2)` MP_TAC THENL
   [MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT]) THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC PALEY_ZYGMUND_INEQUALITY THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC PROB_POSITIVE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bonferroni's inequalities for any finite family of events and any k.      *)
(* ------------------------------------------------------------------------- *)

let BONFERRONI_INEQUALITY = prove
 (`!p:A prob_space (A:K->A->bool) s k.
        FINITE s /\ (!i. i IN s ==> A i IN prob_events p)
        ==> (ODD k ==> prob p (UNIONS (IMAGE A s)) <=
                       sum(1..k) (\j. (-- &1) pow (j + 1) *
                         sum {t | t SUBSET s /\ CARD t = j}
                             (\t. prob p (INTERS (IMAGE A t))))) /\
            (EVEN k ==> sum(1..k) (\j. (-- &1) pow (j + 1) *
                          sum {t | t SUBSET s /\ CARD t = j}
                              (\t. prob p (INTERS (IMAGE A t))))
                        <= prob p (UNIONS (IMAGE A s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (IMAGE (A:K->A->bool) s) IN prob_events p`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_FINITE_UNION_IN_EVENTS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t SUBSET s /\ ~(t = {})
                    ==> INTERS (IMAGE (A:K->A->bool) t) IN prob_events p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PROB_COUNTABLE_INTERS_IN_EVENTS THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[FINITE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j
        ==> integrable p
              (\x. (-- &1) pow (j + 1) *
                   sum {t | t SUBSET s /\ CARD t = j}
                       (\t. indicator_fn
                              (INTERS (IMAGE (A:K->A->bool) t)) x)) /\
            expectation p
              (\x. (-- &1) pow (j + 1) *
                   sum {t | t SUBSET s /\ CARD t = j}
                       (\t. indicator_fn (INTERS (IMAGE A t)) x)) =
            (-- &1) pow (j + 1) *
            sum {t | t SUBSET s /\ CARD t = j}
                (\t. prob p (INTERS (IMAGE A t)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!t. t IN {t | t SUBSET s /\ CARD t = j}
          ==> integrable p (\x. indicator_fn
                                  (INTERS (IMAGE (A:K->A->bool) t)) x) /\
              expectation p (\x. indicator_fn (INTERS (IMAGE A t)) x) =
              prob p (INTERS (IMAGE A t))`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:K->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `INTERS (IMAGE (A:K->A->bool) t) IN prob_events p`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `CARD ({}:K->bool) = j` THEN
        REWRITE_TAC[CARD_CLAUSES] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[ETA_AX; INTEGRABLE_INDICATOR; EXPECTATION_INDICATOR]];
      ALL_TAC] THEN
    SUBGOAL_THEN `FINITE {t | t SUBSET s /\ CARD (t:K->bool) = j}`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `{t | t SUBSET s /\ CARD (t:K->bool) = j}`;
                   `\t x. indicator_fn (INTERS (IMAGE (A:K->A->bool) t)) x`]
           EXPECTATION_SUM_FINITE) THEN
    MP_TAC(ISPECL [`p:A prob_space`;
                   `{t | t SUBSET s /\ CARD (t:K->bool) = j}`;
                   `\t x. indicator_fn (INTERS (IMAGE (A:K->A->bool) t)) x`]
           INTEGRABLE_SUM_FINITE) THEN
    ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `1..k`;
    `\j x. (-- &1) pow (j + 1) *
           sum {t | t SUBSET s /\ CARD t = j}
               (\t. indicator_fn (INTERS (IMAGE (A:K->A->bool) t)) x)`]
    EXPECTATION_SUM_FINITE) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `1..k`;
    `\j x. (-- &1) pow (j + 1) *
           sum {t | t SUBSET s /\ CARD t = j}
               (\t. indicator_fn (INTERS (IMAGE (A:K->A->bool) t)) x)`]
    INTEGRABLE_SUM_FINITE) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..k) (\j. (-- &1) pow (j + 1) *
                   sum {t | t SUBSET s /\ CARD t = j}
                       (\t. prob p (INTERS (IMAGE (A:K->A->bool) t)))) =
    expectation p (\x. sum(1..k) (\j. (-- &1) pow (j + 1) *
                   sum {t | t SUBSET s /\ CARD t = j}
                       (\t. indicator_fn (INTERS (IMAGE A t)) x)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prob p (UNIONS (IMAGE (A:K->A->bool) s)) =
                expectation p (\x. indicator_fn (UNIONS (IMAGE A s)) x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[ETA_AX; EXPECTATION_INDICATOR]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC EXPECTATION_MONO THEN
  ASM_SIMP_TAC[ETA_AX; INTEGRABLE_INDICATOR] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:K->A->bool`; `s:K->bool`; `k:num`; `x:A`]
         BONFERRONI_INDICATOR) THEN
  ASM_SIMP_TAC[]);;
