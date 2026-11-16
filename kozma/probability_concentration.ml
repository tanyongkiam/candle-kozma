(* ========================================================================= *)
(* Concentration inequalities: sums of independent and k-wise independent    *)
(* random variables, and martingales, from L. Kozma, "Useful Inequalities"   *)
(* (v0.44).                                                                  *)
(* ========================================================================= *)

needs "kozma/probability_basic.ml";;
needs "kozma/means.ml";;
needs "kozma/bernoulli_exp.ml";;

(* ------------------------------------------------------------------------- *)
(* Independence of a family of random variables X_i (i IN s, any index set), *)
(* and k-wise independence: every nonempty finite subfamily (of at most k    *)
(* members) has joint CDF equal to the product of the marginal CDFs. This is *)
(* the CDF form of the library's mutually_indep_rv_seq, for which            *)
(* INDEP_RV_FAMILY_SEQ is the bridge.                                        *)
(* ------------------------------------------------------------------------- *)

let indep_rv_family = new_definition
 `indep_rv_family (p:A prob_space) (s:K->bool) (X:K->A->real) <=>
  (!i. i IN s ==> random_variable p (X i)) /\
  (!u z. u SUBSET s /\ FINITE u /\ ~(u = {})
         ==> prob p (INTERS (IMAGE
                (\i. {x | x IN prob_carrier p /\ X i x <= z i}) u)) =
             product u
               (\i. prob p {x | x IN prob_carrier p /\ X i x <= z i}))`;;

let kwise_indep_rv_family = new_definition
 `kwise_indep_rv_family (p:A prob_space) k (s:K->bool) (X:K->A->real) <=>
  (!i. i IN s ==> random_variable p (X i)) /\
  (!u z. u SUBSET s /\ FINITE u /\ ~(u = {}) /\ CARD u <= k
         ==> prob p (INTERS (IMAGE
                (\i. {x | x IN prob_carrier p /\ X i x <= z i}) u)) =
             product u
               (\i. prob p {x | x IN prob_carrier p /\ X i x <= z i}))`;;

let INTERS_IMAGE_CDF_EVENTS = prove
 (`!p:A prob_space (X:K->A->real) u z.
        ~(u = {})
        ==> INTERS (IMAGE (\i. {x | x IN prob_carrier p /\ X i x <= z i}) u) =
            {x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i}`,
  REWRITE_TAC[EXTENSION; INTERS_IMAGE; IN_ELIM_THM] THEN SET_TAC[]);;

let INDEP_RV_FAMILY_ALT = prove
 (`!p:A prob_space (s:K->bool) X.
        indep_rv_family p s X <=>
        (!i. i IN s ==> random_variable p (X i)) /\
        (!u z. u SUBSET s /\ FINITE u
               ==> prob p {x | x IN prob_carrier p /\
                               !i. i IN u ==> X i x <= z i} =
                   product u
                     (\i. prob p {x | x IN prob_carrier p /\ X i x <= z i}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indep_rv_family] THEN AP_TERM_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `u:K->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES] THEN
      REWRITE_TAC[SET_RULE `{x:A | x IN s} = s`; PROB_SPACE];
      ASM_MESON_TAC[INTERS_IMAGE_CDF_EVENTS]];
    ASM_SIMP_TAC[INTERS_IMAGE_CDF_EVENTS]]);;

let KWISE_INDEP_RV_FAMILY_ALT = prove
 (`!p:A prob_space k (s:K->bool) X.
        kwise_indep_rv_family p k s X <=>
        (!i. i IN s ==> random_variable p (X i)) /\
        (!u z. u SUBSET s /\ FINITE u /\ CARD u <= k
               ==> prob p {x | x IN prob_carrier p /\
                               !i. i IN u ==> X i x <= z i} =
                   product u
                     (\i. prob p {x | x IN prob_carrier p /\ X i x <= z i}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kwise_indep_rv_family] THEN AP_TERM_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `u:K->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY; PRODUCT_CLAUSES] THEN
      REWRITE_TAC[SET_RULE `{x:A | x IN s} = s`; PROB_SPACE];
      ASM_MESON_TAC[INTERS_IMAGE_CDF_EVENTS]];
    ASM_SIMP_TAC[INTERS_IMAGE_CDF_EVENTS]]);;

let INDEP_RV_FAMILY_SEQ = prove
 (`!p:A prob_space X.
        mutually_indep_rv_seq p X <=> indep_rv_family p (:num) X`,
  REWRITE_TAC[mutually_indep_rv_seq; indep_rv_family; SUBSET_UNIV; IN_UNIV]);;

let INDEP_RV_FAMILY_SUBSET = prove
 (`!p:A prob_space (s:K->bool) t X.
        indep_rv_family p s X /\ t SUBSET s ==> indep_rv_family p t X`,
  REWRITE_TAC[indep_rv_family] THEN MESON_TAC[SUBSET_TRANS; SUBSET]);;

let KWISE_INDEP_RV_FAMILY_SUBSET = prove
 (`!p:A prob_space k (s:K->bool) t X.
        kwise_indep_rv_family p k s X /\ t SUBSET s
        ==> kwise_indep_rv_family p k t X`,
  REWRITE_TAC[kwise_indep_rv_family] THEN MESON_TAC[SUBSET_TRANS; SUBSET]);;

let INDEP_RV_FAMILY_IMP_KWISE = prove
 (`!p:A prob_space k (s:K->bool) X.
        indep_rv_family p s X ==> kwise_indep_rv_family p k s X`,
  SIMP_TAC[indep_rv_family; kwise_indep_rv_family]);;

let KWISE_INDEP_RV_FAMILY_MONO = prove
 (`!p:A prob_space k l (s:K->bool) X.
        kwise_indep_rv_family p l s X /\ k <= l
        ==> kwise_indep_rv_family p k s X`,
  REWRITE_TAC[kwise_indep_rv_family] THEN MESON_TAC[LE_TRANS]);;

let KWISE_INDEP_RV_FAMILY_EQ_INDEP = prove
 (`!p:A prob_space k (s:K->bool) X.
        FINITE s /\ CARD s <= k
        ==> (kwise_indep_rv_family p k s X <=> indep_rv_family p s X)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[kwise_indep_rv_family; indep_rv_family] THEN AP_TERM_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CARD_SUBSET; LE_TRANS]);;

let KWISE_INDEP_RV_FAMILY_IMP_INDEP = prove
 (`!p:A prob_space k (s:K->bool) t X.
        kwise_indep_rv_family p k s X /\ t SUBSET s /\ FINITE t /\ CARD t <= k
        ==> indep_rv_family p t X`,
  MESON_TAC[KWISE_INDEP_RV_FAMILY_SUBSET; KWISE_INDEP_RV_FAMILY_EQ_INDEP]);;

let INDEP_RV_FAMILY_PAIR = prove
 (`!p:A prob_space (X:K->A->real) i j.
        ~(i = j) ==> (indep_rv_family p {i,j} X <=> indep_rv p (X i) (X j))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(j:K = i)` ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN REWRITE_TAC[INDEP_RV_FAMILY_ALT; indep_rv] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
                 `(a /\ b ==> (c <=> d))
                  ==> (a /\ b /\ c <=> a /\ b /\ d)`) THEN
  STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC[`a:real`; `b:real`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL[`{i:K,j}`;
                                 `\m:K. if m = i then a:real else b`]) THEN
    REWRITE_TAC[SUBSET_REFL; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `!f. product {i:K,j} f = f i * f j`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SIMP_TAC[PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING;
               NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC];
    MAP_EVERY X_GEN_TAC[`u:K->bool`; `z:K->real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `u = {} \/ u = {i:K} \/ u = {j} \/ u = {i,j}` MP_TAC THENL
     [UNDISCH_TAC `u SUBSET {i:K,j}` THEN SET_TAC[];
      ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING;
             NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; SET_RULE `{x:A | x IN s} = s`;
                    PROB_SPACE]]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint blocks of an independent family are independent: the sigma-      *)
(* algebras generated by the CDF events of the variables in each block are   *)
(* independent.                                                              *)
(* ------------------------------------------------------------------------- *)

let CDF_BOX_IN_EVENTS = prove
 (`!p:A prob_space (X:K->A->real) u z.
        FINITE u /\ (!i. i IN u ==> random_variable p (X i))
        ==> {x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i}
            IN prob_events p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[SET_RULE `{x:A | x IN s} = s`; PROB_CARRIER_IN_EVENTS] THEN
  MAP_EVERY X_GEN_TAC[`a:K`; `s:K->bool`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier p /\ X (a:K) x <= z a /\
      !i. i IN s ==> (X:K->A->real) i x <= z i} =
     {x | x IN prob_carrier p /\ X a x <= z a} INTER
     {x | x IN prob_carrier p /\ !i. i IN s ==> X i x <= z i}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN GEN_TAC THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN CONJ_TAC THENL
   [UNDISCH_TAC `random_variable p ((X:K->A->real) a)` THEN
    SIMP_TAC[random_variable];
    ASM_SIMP_TAC[]]);;

let BOXES_PI_SYSTEM = prove
 (`!U:A->bool (X:K->A->real) t.
     pi_system {{x | x IN U /\ !i. i IN u ==> X i x <= z i} |
                u SUBSET t /\ FINITE u /\ z IN (:K->real)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pi_system; IN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC[`U:A->bool`; `{}:K->bool`; `z:K->real`] THEN
    REWRITE_TAC[EMPTY_SUBSET; FINITE_EMPTY; NOT_IN_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `u1:K->bool` THEN REPEAT DISCH_TAC THEN X_GEN_TAC `z1:K->real` THEN
  X_GEN_TAC `u2:K->bool` THEN REPEAT DISCH_TAC THEN X_GEN_TAC `z2:K->real` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC[`u1 UNION u2:K->bool`;
                       `\i:K. if i IN u1 then if i IN u2
                              then min (z1 i) (z2 i) else z1 i else z2 i`] THEN
  ASM_REWRITE_TAC[UNION_SUBSET; FINITE_UNION] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `x:A` THEN ASM_CASES_TAC `x IN (U:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o check(fun th ->
        can(term_match[] `!i:K. P i \/ Q i ==> R i`) (concl th)))) THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_MIN] THEN ASM_MESON_TAC[]);;

let CDF_BOXES_PI_SYSTEM = prove
 (`!p:A prob_space (X:K->A->real) t.
     pi_system {{x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i} |
                u SUBSET t /\ FINITE u /\ z IN (:K->real)}`,
  REWRITE_TAC[BOXES_PI_SYSTEM]);;

let CDF_BOXES_GENERATE = prove
 (`!p:A prob_space (X:K->A->real) t.
     (!i. i IN t ==> random_variable p (X i))
     ==> UNIONS {{x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i} |
                 u SUBSET t /\ FINITE u /\ z IN (:K->real)} = prob_carrier p /\
         {{x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i} |
          u SUBSET t /\ FINITE u /\ z IN (:K->real)} SUBSET prob_events p /\
         sigma_generated (prob_carrier p)
           {{x | x IN prob_carrier p /\ X i x <= v} | i IN t /\ v IN (:real)}
         SUBSET
         sigma_generated (prob_carrier p)
           {{x | x IN prob_carrier p /\ !i. i IN u ==> X i x <= z i} |
            u SUBSET t /\ FINITE u /\ z IN (:K->real)}`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [SET_TAC[];
      ALL_TAC] THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC[`{}:K->bool`; `z:K->real`] THEN
    REWRITE_TAC[EMPTY_SUBSET; FINITE_EMPTY; NOT_IN_EMPTY; IN_UNIV] THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CDF_BOX_IN_EVENTS THEN ASM SET_TAC[];
    MATCH_MP_TAC SIGMA_GENERATED_MONO THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC[`j:K`; `v:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC[`{j:K}`; `\i:K. v:real`] THEN
    ASM_REWRITE_TAC[SING_SUBSET; FINITE_SING; IN_SING; FORALL_UNWIND_THM2]]);;

let INDEP_RV_FAMILY_BLOCKS = prove
 (`!p:A prob_space (X:K->A->real) t1 t2 a b.
     indep_rv_family p (t1 UNION t2) X /\ DISJOINT t1 t2 /\
     a IN sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} |
             i IN t1 /\ v IN (:real)} /\
     b IN sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} | i IN t2 /\ v IN (:real)}
     ==> prob p (a INTER b) = prob p a * prob p b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I[INDEP_RV_FAMILY_ALT]) THEN
  MAP_EVERY(fun t -> MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; t]
                              CDF_BOXES_GENERATE) THEN ANTS_TAC THENL
             [ASM SET_TAC[];
              STRIP_TAC]) [`t1:K->bool`; `t2:K->bool`] THEN
  MAP_EVERY ABBREV_TAC
   [`P1 = {{x | x IN prob_carrier p /\
                !i. i IN u ==> (X:K->A->real) i x <= z i} |
           u SUBSET t1 /\ FINITE u /\ z IN (:K->real)}`;
    `P2 = {{x | x IN prob_carrier p /\
                !i. i IN u ==> (X:K->A->real) i x <= z i} |
           u SUBSET t2 /\ FINITE u /\ z IN (:K->real)}`] THEN
  MAP_EVERY(fun t -> MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; t]
                              CDF_BOXES_PI_SYSTEM) THEN ASM_REWRITE_TAC[] THEN
            DISCH_TAC) [`t1:K->bool`; `t2:K->bool`] THEN
  SUBGOAL_THEN
    `!c d. c IN P1 /\ d IN P2
           ==> prob p (c INTER d) = prob p c * prob p (d:A->bool)`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC["P1"; "P2"] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `u1:K->bool` THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `z1:K->real` THEN X_GEN_TAC `u2:K->bool` THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `z2:K->real` THEN
    SUBGOAL_THEN
      `{x | x IN prob_carrier p /\ !i. i IN u1 ==> (X:K->A->real) i x <= z1 i}
       INTER
       {x | x IN prob_carrier p /\ !i. i IN u2 ==> X i x <= z2 i} =
       {x | x IN prob_carrier p /\
        !i. i IN u1 UNION u2
            ==> X i x <= (\i. if i IN u1 then z1 i else z2 i) i}`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:A` THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o
                             check(fun th -> can(term_match[]
                                   `!i:K. P i \/ Q i ==> R i`)
                                     (concl th)))) THEN
      REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN SUBGOAL_THEN `DISJOINT (u1:K->bool) u2` ASSUME_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL[`u1 UNION u2:K->bool`;
                               `\i:K. if i IN u1 then z1 i
                                      else (z2:K->real) i`]) THEN
    FIRST_ASSUM(MP_TAC o SPECL[`u1:K->bool`; `z1:K->real`]) THEN
    FIRST_ASSUM(MP_TAC o SPECL[`u2:K->bool`; `z2:K->real`]) THEN ANTS_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN ANTS_TAC THENL
     [ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION] THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC[PRODUCT_UNION] THEN
    BINOP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:K` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!c d. c IN P1 /\ d IN sigma_generated (prob_carrier p) P2
           ==> prob p (c INTER d) = prob p c * prob p (d:A->bool)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `c:A->bool`; `P2:(A->bool)->bool`]
             INDEP_EXTENDS_TO_SIGMA) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!c d. c IN sigma_generated (prob_carrier p) P1 /\
           d IN sigma_generated (prob_carrier p) P2
           ==> prob p (c INTER d) = prob p c * prob p (d:A->bool)`
    MP_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `d:A->bool`; `P1:(A->bool)->bool`]
             INDEP_EXTENDS_TO_SIGMA) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SIGMA_GENERATED_SUBSET_EVENTS; SUBSET];
        ALL_TAC] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let KWISE_INDEP_RV_FAMILY_BLOCKS = prove
 (`!p:A prob_space (X:K->A->real) k t1 t2 a b.
     kwise_indep_rv_family p k (t1 UNION t2) X /\ FINITE (t1 UNION t2) /\
     CARD (t1 UNION t2) <= k /\ DISJOINT t1 t2 /\
     a IN sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} |
             i IN t1 /\ v IN (:real)} /\
     b IN sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} |
             i IN t2 /\ v IN (:real)}
     ==> prob p (a INTER b) = prob p a * prob p b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEP_RV_FAMILY_BLOCKS THEN
  MAP_EVERY EXISTS_TAC [`X:K->A->real`; `t1:K->bool`; `t2:K->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_IMP_INDEP THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `t1 UNION t2:K->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Measurability with respect to the sigma-algebra of a block, and           *)
(* expectations of products: E[prod Y_i] = prod E[Y_i] for bounded Y_i, each *)
(* a function of X_i, over an independent family (and over at most k members *)
(* of a k-wise independent one).                                             *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_WRT_RESTRICT = prove
 (`!p:A prob_space G f.
        sub_sigma_algebra p G
        ==> (measurable_wrt p G f <=>
             random_variable (restrict_prob_space p G) f)`,
  SIMP_TAC[measurable_wrt; random_variable; RESTRICT_PROB_SPACE_CARRIER;
           RESTRICT_PROB_SPACE_EVENTS]);;

let MEASURABLE_WRT_BOREL_MEASURABLE_COMPOSE = prove
 (`!p:A prob_space G f g.
        sub_sigma_algebra p G /\ measurable_wrt p G f /\
        borel_measurable_map (euclideanreal,euclideanreal) g
        ==> measurable_wrt p G (\x. g(f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `G:(A->bool)->bool`; `f:A->real`]
           MEASURABLE_WRT_RESTRICT) THEN
  MP_TAC(ISPECL[`p:A prob_space`; `G:(A->bool)->bool`;
                `\x:A. (g:real->real)(f x)`] MEASURABLE_WRT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC RANDOM_VARIABLE_BOREL_MEASURABLE_COMPOSE THEN
  ASM_REWRITE_TAC[]);;

let MEASURABLE_WRT_COMP_CONTINUOUS = prove
 (`!p:A prob_space G f g.
        sub_sigma_algebra p G /\ measurable_wrt p G f /\
        g real_continuous_on (:real)
        ==> measurable_wrt p G (\x. g(f x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_WRT_BOREL_MEASURABLE_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_IMP_BOREL_MEASURABLE_MAP THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEANREAL]);;

let MEASURABLE_WRT_PRODUCT = prove
 (`!p:A prob_space G (f:K->A->real) s.
        sub_sigma_algebra p G /\ FINITE s /\
        (!i. i IN s ==> measurable_wrt p G (f i))
        ==> measurable_wrt p G (\x. product s (\i. f i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; MEASURABLE_WRT_CONST; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `G:(A->bool)->bool`; `(f:K->A->real) x`;
                `\x. product s (\i. (f:K->A->real) i x)`]
           MEASURABLE_WRT_MUL) THEN ASM_SIMP_TAC[]);;

let MEASURABLE_WRT_SUM_FINITE = prove
 (`!p:A prob_space G (f:K->A->real) s.
        sub_sigma_algebra p G /\ FINITE s /\
        (!i. i IN s ==> measurable_wrt p G (f i))
        ==> measurable_wrt p G (\x. sum s (\i. f i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `sub_sigma_algebra (p:A prob_space) G` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; MEASURABLE_WRT_CONST; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `G:(A->bool)->bool`; `(f:K->A->real) x`;
                `\x. sum s (\i. (f:K->A->real) i x)`] MEASURABLE_WRT_ADD) THEN
  ASM_SIMP_TAC[]);;

let SUB_SIGMA_ALGEBRA_CDF_GENERATED = prove
 (`!p:A prob_space (X:K->A->real) t.
        (!i. i IN t ==> random_variable p (X i))
        ==> sub_sigma_algebra p
              (sigma_generated (prob_carrier p)
                 {{x | x IN prob_carrier p /\ X i x <= v} |
                  i IN t /\ v IN (:real)})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sub_sigma_algebra] THEN
  SUBGOAL_THEN
    `!a. a IN
         {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
          i IN t /\ v IN (:real)}
         ==> a SUBSET prob_carrier p`
    ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIGMA_GENERATED_IS_SIGMA_ALGEBRA; SIGMA_GENERATED_CARRIER] THEN
  MATCH_MP_TAC SIGMA_GENERATED_SUBSET_EVENTS THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o check(is_forall o concl)) THEN
  ASM_SIMP_TAC[random_variable]);;

let MEASURABLE_WRT_CDF_GENERATED = prove
 (`!p:A prob_space (X:K->A->real) t i.
        i IN t
        ==> measurable_wrt p
              (sigma_generated (prob_carrier p)
                 {{x | x IN prob_carrier p /\ X i x <= v} |
                  i IN t /\ v IN (:real)})
              (X i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_wrt] THEN
  X_GEN_TAC `v:real` THEN MATCH_MP_TAC IN_SIGMA_GENERATED_GEN THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[]);;

let CDF_GENERATED_MONO = prove
 (`!p:A prob_space (X:K->A->real) t u.
        t SUBSET u
        ==> sigma_generated (prob_carrier p)
              {{x | x IN prob_carrier p /\ X i x <= v} |
               i IN t /\ v IN (:real)}
            SUBSET
            sigma_generated (prob_carrier p)
              {{x | x IN prob_carrier p /\ X i x <= v} |
               i IN u /\ v IN (:real)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGMA_GENERATED_MONO THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN ASM SET_TAC[]);;

let CDF_GENERATED_SING = prove
 (`!p:A prob_space (X:K->A->real) i.
        {{x | x IN prob_carrier p /\ X j x <= v} | j IN {i} /\ v IN (:real)} =
        {{x | x IN prob_carrier p /\ X i x <= v} | v IN (:real)}`,
  REWRITE_TAC[IN_SING] THEN SET_TAC[]);;

let INDEP_RV_FAMILY_BLOCKS_INDEP_RV = prove
 (`!p:A prob_space (X:K->A->real) t1 t2 f g.
     indep_rv_family p (t1 UNION t2) X /\ DISJOINT t1 t2 /\
     measurable_wrt p (sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} |
             i IN t1 /\ v IN (:real)}) f /\
     measurable_wrt p (sigma_generated (prob_carrier p)
            {{x | x IN prob_carrier p /\ X i x <= v} |
             i IN t2 /\ v IN (:real)}) g
     ==> indep_rv p f g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE
                I[indep_rv_family]) THEN REWRITE_TAC[indep_rv] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC
      `sigma_generated (prob_carrier p)
         {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
          i IN t1 /\ v IN (:real)}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC
      `sigma_generated (prob_carrier p)
         {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
          i IN t2 /\ v IN (:real)}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC[`a:real`; `b:real`] THEN
    SUBGOAL_THEN
      `{x | x IN prob_carrier p /\ (f:A->real) x <= a /\
            (g:A->real) x <= b} =
       {x | x IN prob_carrier p /\ f x <= a} INTER
       {x | x IN prob_carrier p /\ g x <= b}`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INDEP_RV_FAMILY_BLOCKS THEN
    MAP_EVERY EXISTS_TAC[`X:K->A->real`; `t1:K->bool`; `t2:K->bool`] THEN
    ASM_MESON_TAC[measurable_wrt]]);;

let INDEP_RV_FAMILY_PRODUCT_INDUCT = prove
 (`!p:A prob_space (X:K->A->real) Y s.
    FINITE s
    ==> indep_rv_family p s X /\
        (!i. i IN s ==> measurable_wrt p (sigma_generated (prob_carrier p)
                          {{x | x IN prob_carrier p /\ X i x <= v} |
                           v IN (:real)}) (Y i) /\
                        ?B. almost_surely p {x | abs(Y i x) <= B})
        ==> measurable_wrt p (sigma_generated (prob_carrier p)
                  {{x | x IN prob_carrier p /\ X i x <= v} |
                   i IN s /\ v IN (:real)})
                  (\x. product s (\i. Y i x)) /\
            (?B. almost_surely p {x | abs(product s (\i. Y i x)) <= B}) /\
            integrable p (\x. product s (\i. Y i x)) /\
            expectation p (\x. product s (\i. Y i x)) =
            product s (\i. expectation p (Y i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES] THEN STRIP_TAC THEN
    REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_CONST THEN
      MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
      REWRITE_TAC[NOT_IN_EMPTY];
      EXISTS_TAC `&1` THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun ih -> DISCH_THEN(fun th -> MP_TAC(MATCH_MP ih
    (CONJ (MATCH_MP INDEP_RV_FAMILY_SUBSET
             (CONJ (CONJUNCT1 th) (SET_RULE `s SUBSET (a:K) INSERT s`)))
          (CONJUNCT2(CONJUNCT2 th)))) THEN ASSUME_TAC th)) THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  ABBREV_TAC `P = \x:A. product s (\i:K. (Y:K->A->real) i x)` THEN
  SUBGOAL_THEN `!x:A. product s (\i:K. (Y:K->A->real) i x) = P x`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CDF_GENERATED_SING]) THEN
  SUBGOAL_THEN
   `!i. i IN (a:K) INSERT s ==> random_variable p ((X:K->A->real) i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[indep_rv_family]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t SUBSET (a:K) INSERT s
        ==> sub_sigma_algebra p (sigma_generated (prob_carrier p)
              {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
               i IN t /\ v IN (:real)})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable_wrt p (sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       i IN (a:K) INSERT s /\ v IN (:real)}) ((Y:K->A->real) a) /\
    measurable_wrt p (sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       i IN (a:K) INSERT s /\ v IN (:real)}) P`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN
      CONJ_TAC THENL
       [ACCEPT_TAC th; MATCH_MP_TAC CDF_GENERATED_MONO THEN SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable_wrt p (sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       i IN (a:K) INSERT s /\ v IN (:real)}) (\x. (Y:K->A->real) a x * P x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_MUL THEN ASM_SIMP_TAC[SUBSET_REFL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `random_variable p ((Y:K->A->real) a) /\ random_variable p (P:A->real) /\
    random_variable p (\x. (Y:K->A->real) a x * P x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       i IN (a:K) INSERT s /\ v IN (:real)}` THEN
    ASM_SIMP_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `almost_surely p {x:A | abs((Y:K->A->real) a x * P x) <= abs B' * abs B}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
     `{x:A | abs((Y:K->A->real) a x) <= B'} INTER {x | abs(P x) <= B}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_INTER; IN_INTER; IN_ELIM_THM; REAL_ABS_MUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integrable p ((Y:K->A->real) a) /\
    integrable p (\x. (Y:K->A->real) a x * P x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
    `expectation (p:A prob_space) P = product (s:K->bool) f`) (concl th))) THEN
  MATCH_MP_TAC EXPECTATION_PRODUCT_INDEP THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INDEP_RV_FAMILY_BLOCKS_INDEP_RV THEN
  MAP_EVERY EXISTS_TAC [`X:K->A->real`; `{a:K}`; `s:K->bool`] THEN
  ASM_REWRITE_TAC[SET_RULE `{a:K} UNION s = a INSERT s`] THEN ASM SET_TAC[]);;

let INDEP_RV_FAMILY_EXPECTATION_PRODUCT = prove
 (`!p:A prob_space (X:K->A->real) Y s.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> measurable_wrt p (sigma_generated (prob_carrier p)
                      {{x | x IN prob_carrier p /\ X i x <= v} |
                       v IN (:real)}) (Y i) /\
                    ?B. almost_surely p {x | abs(Y i x) <= B})
    ==> integrable p (\x. product s (\i. Y i x)) /\
        expectation p (\x. product s (\i. Y i x)) =
        product s (\i. expectation p (Y i))`,
  MESON_TAC[INDEP_RV_FAMILY_PRODUCT_INDUCT]);;

let KWISE_INDEP_RV_FAMILY_EXPECTATION_PRODUCT = prove
 (`!p:A prob_space (X:K->A->real) Y k s u.
    kwise_indep_rv_family p k s X /\ u SUBSET s /\ FINITE u /\ CARD u <= k /\
    (!i. i IN u ==> measurable_wrt p (sigma_generated (prob_carrier p)
                      {{x | x IN prob_carrier p /\ X i x <= v} |
                       v IN (:real)}) (Y i) /\
                    ?B. almost_surely p {x | abs(Y i x) <= B})
    ==> integrable p (\x. product u (\i. Y i x)) /\
        expectation p (\x. product u (\i. Y i x)) =
        product u (\i. expectation p (Y i))`,
  MESON_TAC[INDEP_RV_FAMILY_EXPECTATION_PRODUCT;
            KWISE_INDEP_RV_FAMILY_IMP_INDEP]);;

let MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS = prove
 (`!p:A prob_space X g.
        random_variable p X /\ g real_continuous_on (:real)
        ==> measurable_wrt p (sigma_generated (prob_carrier p)
                {{x | x IN prob_carrier p /\ X x <= v} |
                 v IN (:real)}) (\x. g(X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(\i:num. X):num->A->real`; `{0}`]
           SUB_SIGMA_ALGEBRA_CDF_GENERATED) THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(\i:num. X):num->A->real`; `{0}`; `0`]
           MEASURABLE_WRT_CDF_GENERATED) THEN
  ASM_REWRITE_TAC[CDF_GENERATED_SING; IN_SING; FORALL_UNWIND_THM2] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_COMP_CONTINUOUS THEN
  ASM_REWRITE_TAC[]);;

let INDEP_RV_FAMILY_EXPECTATION_PRODUCT_CONTINUOUS = prove
 (`!p:A prob_space (X:K->A->real) g s.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> g i real_continuous_on (:real) /\
                    ?B. almost_surely p {x | abs(g i (X i x)) <= B})
    ==> integrable p (\x. product s (\i. g i (X i x))) /\
        expectation p (\x. product s (\i. g i (X i x))) =
        product s (\i. expectation p (\x. g i (X i x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`;
                `\i:K x:A. (g:K->real->real) i (X i x)`; `s:K->bool`]
           INDEP_RV_FAMILY_EXPECTATION_PRODUCT) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o check(is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE
                    I[indep_rv_family]) THEN ASM_SIMP_TAC[ETA_AX];
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Laws of families: equal joint CDFs on boxes give equal joint laws on the  *)
(* box sigma-algebra; independent families with equal marginals have equal   *)
(* joint CDFs; measurable functions of the members of an independent family  *)
(* form an independent family.                                               *)
(* ------------------------------------------------------------------------- *)

let POINT_MASS_PROB_SPACE = prove
 (`!(E:(A->bool)->bool) y0.
        sigma_algebra E /\ y0 IN UNIONS E
        ==> prob_events (prob_space (E,\c. if y0 IN c then &1 else &0)) = E /\
            prob_carrier (prob_space (E,\c. if y0 IN c then &1 else &0)) =
            UNIONS E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(E:(A->bool)->bool,\c:A->bool. if y0 IN c then &1 else &0)`
           (CONJUNCT2 prob_space_tybij)) THEN REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN X_GEN_TAC `B:num->A->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `?k. (y0:A) IN (B:num->A->bool) k` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `k:num`) THEN
      SUBGOAL_THEN `!n. (y0:A) IN (B:num->A->bool) n <=> n = k`
        ASSUME_TAC THENL
       [GEN_TAC THEN EQ_TAC THENL
         [ALL_TAC;
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL[`n:num`; `k:num`] o
                        check(is_forall o concl)) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y0:A) IN UNIONS {(B:num->A->bool) n | n IN (:num)}`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SERIES_SUM THEN
      EXISTS_TAC `{k:num}` THEN
      REWRITE_TAC[FINITE_SING; FROM_0; SUBSET_UNIV; IN_SING; SUM_SING] THEN
      SIMP_TAC[];
      SUBGOAL_THEN `~((y0:A) IN UNIONS {(B:num->A->bool) n | n IN (:num)})`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!n. ~((y0:A) IN (B:num->A->bool) n)`
        (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[];
        REWRITE_TAC[REAL_SERIES_0]]];
    DISCH_TAC THEN REWRITE_TAC[prob_carrier; prob_events] THEN
    ASM_REWRITE_TAC[]]);;

let RANDOM_VARIABLE_SUM_FINITE = prove
 (`!p:A prob_space (X:K->A->real) s.
        FINITE s /\ (!i. i IN s ==> random_variable p (X i))
        ==> random_variable p (\x. sum s (\i. X i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; RANDOM_VARIABLE_CONST; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) x`;
                `\y. sum s (\i. (X:K->A->real) i y)`] RANDOM_VARIABLE_ADD) THEN
  ASM_SIMP_TAC[]);;

let BOX_SIGMA_ALGEBRA_SUM_GE = prove
 (`!s:K->bool d.
        FINITE s
        ==> {y | sum s y >= d} IN
            sigma_generated (:K->real) {{y | y i <= v} |
                                        i IN s /\ v IN (:real)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = {{y:K->real | y i <= v} | i IN s /\ v IN (:real)}` THEN
  MP_TAC(ISPECL[`sigma_generated (:K->real) G`; `ARB:K->real`]
           POINT_MASS_PROB_SPACE) THEN
  SIMP_TAC[SIGMA_GENERATED_IS_SIGMA_ALGEBRA; SIGMA_GENERATED_CARRIER;
           SUBSET_UNIV; IN_UNIV] THEN
  ABBREV_TAC
    `q =
     prob_space (sigma_generated (:K->real) G,
                 \c:(K->real)->bool. if ARB IN c then &1 else &0)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL[`q:(K->real) prob_space`; `sum (s:K->bool)`; `d:real`]
           RV_PREIMAGE_GE) THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL[`q:(K->real) prob_space`; `\i:K y:K->real. y i`; `s:K->bool`]
           RANDOM_VARIABLE_SUM_FINITE) THEN ASM_REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[random_variable; IN_UNIV] THEN X_GEN_TAC `a:real` THEN
  MATCH_MP_TAC IN_SIGMA_GENERATED_GEN THEN EXPAND_TAC "G" THEN
  REWRITE_TAC[SUBSET_UNIV; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[]);;

let JOINT_LAW_EQ_BOXES = prove
 (`!p:A prob_space (X:K->A->real) Y s.
     (!i. i IN s ==> random_variable p (X i) /\ random_variable p (Y i)) /\
     (!u z. u SUBSET s /\ FINITE u
            ==> prob p {x | x IN prob_carrier p /\
                            !i. i IN u ==> X i x <= z i} =
                prob p {x | x IN prob_carrier p /\
                            !i. i IN u ==> Y i x <= z i})
     ==> !c. c IN sigma_generated (:K->real) {{y | y i <= v} |
                                              i IN s /\ v IN (:real)}
             ==> {x | x IN prob_carrier p /\ (\i. X i x) IN c}
                 IN prob_events p /\
                 {x | x IN prob_carrier p /\ (\i. Y i x) IN c}
                 IN prob_events p /\
                 prob p {x | x IN prob_carrier p /\ (\i. X i x) IN c} =
                 prob p {x | x IN prob_carrier p /\ (\i. Y i x) IN c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Pb = {{y | y IN (:K->real) /\ !i. i IN u ==> y i <= z i} |
                    u SUBSET s /\ FINITE u /\ z IN (:K->real)}` THEN
  ABBREV_TAC
   `L = {c | {x | x IN prob_carrier p /\ (\i. (X:K->A->real) i x) IN c}
             IN prob_events p /\
             {x | x IN prob_carrier p /\ (\i. (Y:K->A->real) i x) IN c}
             IN prob_events p /\
             prob p {x | x IN prob_carrier p /\ (\i. X i x) IN c} =
             prob p {x | x IN prob_carrier p /\ (\i. Y i x) IN c}}` THEN
  SUBGOAL_THEN
   `sigma_generated (:K->real) {{y | y i <= v} |
                                i IN s /\ v IN (:real)} SUBSET L`
  MP_TAC THENL
   [ALL_TAC; EXPAND_TAC "L" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `sigma_generated (:K->real) Pb` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIGMA_GENERATED_MONO THEN REWRITE_TAC[SUBSET_UNIV] THEN
    EXPAND_TAC "Pb" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`j:K`; `v:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`{j:K}`; `\i:K. v:real`] THEN
    ASM_REWRITE_TAC[SING_SUBSET; FINITE_SING; IN_SING; FORALL_UNWIND_THM2;
                    IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC DYNKIN_PI_LAMBDA THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Pb" THEN REWRITE_TAC[BOXES_PI_SYSTEM];
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_UNIV] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNIV] THEN X_GEN_TAC `y:K->real` THEN
    EXISTS_TAC `(:K->real)` THEN REWRITE_TAC[IN_UNIV] THEN EXPAND_TAC "Pb" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`{}:K->bool`; `y:K->real`] THEN
    REWRITE_TAC[EMPTY_SUBSET; FINITE_EMPTY; NOT_IN_EMPTY; IN_UNIV] THEN
    SET_TAC[];
    EXPAND_TAC "L" THEN REWRITE_TAC[lambda_system; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[SET_RULE `{x:A | x IN s /\ T} = s`;
                PROB_CARRIER_IN_EVENTS] THEN
    REWRITE_TAC[SET_RULE `{x:A | x IN s} = s`; PROB_CARRIER_IN_EVENTS] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `c:(K->real)->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      ONCE_REWRITE_TAC[SET_RULE
        `{x:A | x IN s /\ ~P x} = s DIFF {x | x IN s /\ P x}`] THEN
      ASM_SIMP_TAC[PROB_COMPL_IN_EVENTS; PROB_COMPL];
      ALL_TAC] THEN
    X_GEN_TAC `B:num->(K->real)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!Z:K->A->real.
        {x | x IN prob_carrier p /\ (\i. Z i x) IN UNIONS {B n | n | T}} =
        UNIONS {{x | x IN prob_carrier p /\ (\i. Z i x) IN B n} |
                n IN (:num)}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!Z:K->A->real.
        (!n. {x | x IN prob_carrier p /\
                  (\i. Z i x) IN (B:num->(K->real)->bool) n}
             IN prob_events p) /\
        (!m n. ~(m = n) ==> DISJOINT (B m) (B n))
        ==> UNIONS {{x | x IN prob_carrier p /\ (\i. Z i x) IN B n} |
                    n IN (:num)}
              IN prob_events p /\
            ((\n. prob p {x | x IN prob_carrier p /\ (\i. Z i x) IN B n})
             real_sums
             prob p (UNIONS {{x | x IN prob_carrier p /\ (\i. Z i x) IN B n} |
                             n IN (:num)})) (from 0)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
        ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV];
        MP_TAC(ISPECL [`p:A prob_space`;
          `\n. {x | x IN prob_carrier p /\
                    (\i. (Z:K->A->real) i x) IN (B:num->(K->real)->bool) n}`]
          PROB_COUNTABLY_ADDITIVE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. prob p {x | x IN prob_carrier p /\
                       (\i. (X:K->A->real) i x) IN
                       (B:num->(K->real)->bool) n}`;
      `from 0`] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `(\n. prob p {x | x IN prob_carrier p /\
                       (\i. (X:K->A->real) i x) IN
                       (B:num->(K->real)->bool) n}) =
      (\n. prob p {x | x IN prob_carrier p /\
                       (\i. (Y:K->A->real) i x) IN B n})`
    SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM]; ASM_SIMP_TAC[]];
    MAP_EVERY EXPAND_TAC ["Pb"; "L"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`u:K->bool`; `z:K->real`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CDF_BOX_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CDF_BOX_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[SUBSET]]]);;

let PRODUCT_INDICATOR = prove
 (`!(a:K->A->bool) u (y:A).
        FINITE u
        ==> product u (\i. indicator_fn (a i) y) =
            if !i. i IN u ==> y IN a i then &1 else &0`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[indicator_fn] THEN
  ASM_CASES_TAC `(y:A) IN a (x:K)` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MEASURABLE_WRT_LE_IN = prove
 (`!p:A prob_space G f c.
        measurable_wrt p G f ==> {x | x IN prob_carrier p /\ f x <= c} IN G`,
  SIMP_TAC[measurable_wrt]);;

let INDEP_RV_FAMILY_COMPOSE = prove
 (`!p:A prob_space (X:K->A->real) Y s.
        indep_rv_family p s X /\
        (!i. i IN s ==> measurable_wrt p (sigma_generated (prob_carrier p)
                          {{x | x IN prob_carrier p /\ X i x <= v} |
                           v IN (:real)}) (Y i))
        ==> indep_rv_family p s Y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN s ==> sub_sigma_algebra p (sigma_generated (prob_carrier p)
                     {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
                      v IN (:real)})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CDF_GENERATED_SING] THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [indep_rv_family]) THEN
    REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INDEP_RV_FAMILY_ALT] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_WRT_IMP_RV]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:K->bool`; `z:K->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `X:K->A->real`;
    `\i:K. indicator_fn
             {x | x IN prob_carrier p /\ (Y:K->A->real) i x <= z i}`;
    `u:K->bool`] INDEP_RV_FAMILY_EXPECTATION_PRODUCT) THEN
  ASM_SIMP_TAC[PRODUCT_INDICATOR] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[INDEP_RV_FAMILY_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:K) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_INDICATOR THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_LE_IN THEN
      REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; indicator_fn] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!i. i IN u ==> {x | x IN prob_carrier p /\ (Y:K->A->real) i x <= z i}
                   IN prob_events p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(i:K) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_IN_EVENTS THEN
    EXISTS_TAC `sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       v IN (:real)}` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MEASURABLE_WRT_LE_IN THEN
    REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product u (\i. expectation p
       (indicator_fn {x | x IN prob_carrier p /\ (Y:K->A->real) i x <= z i})) =
    product u (\i. prob p {x | x IN prob_carrier p /\ Y i x <= z i})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[EXPECTATION_INDICATOR];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `expectation p (indicator_fn
    {x | x IN prob_carrier p /\
         !i. i IN u ==> (Y:K->A->real) i x <= z i})` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXPECTATION_INDICATOR THEN
    MATCH_MP_TAC CDF_BOX_IN_EVENTS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `sigma_generated (prob_carrier p)
      {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
       v IN (:real)}` THEN
    SUBGOAL_THEN `(i:K) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC EXPECTATION_EXT THEN
    REWRITE_TAC[indicator_fn; IN_ELIM_THM] THEN SIMP_TAC[]]);;

let KWISE_INDEP_RV_FAMILY_COMPOSE = prove
 (`!p:A prob_space (X:K->A->real) Y k s.
        kwise_indep_rv_family p k s X /\
        (!i. i IN s ==> measurable_wrt p (sigma_generated (prob_carrier p)
                          {{x | x IN prob_carrier p /\ X i x <= v} |
                           v IN (:real)}) (Y i))
        ==> kwise_indep_rv_family p k s Y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KWISE_INDEP_RV_FAMILY_ALT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN MATCH_MP_TAC MEASURABLE_WRT_IMP_RV THEN
    EXISTS_TAC `sigma_generated (prob_carrier p)
                  {{x | x IN prob_carrier p /\ (X:K->A->real) i x <= v} |
                   v IN (:real)}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM CDF_GENERATED_SING] THEN
    MATCH_MP_TAC SUB_SIGMA_ALGEBRA_CDF_GENERATED THEN
    REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:K->bool`; `z:K->real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `indep_rv_family p u (Y:K->A->real)` MP_TAC THENL
   [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_IMP_INDEP THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s:K->bool`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INDEP_RV_FAMILY_ALT] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let INDEP_RV_FAMILY_JOINT_CDF = prove
 (`!p:A prob_space (X:K->A->real) Y s.
        indep_rv_family p s X /\ indep_rv_family p s Y /\
        (!i c. i IN s
               ==> distribution_fn p (X i) c = distribution_fn p (Y i) c)
        ==> !u z. u SUBSET s /\ FINITE u
                  ==> prob p {x | x IN prob_carrier p /\
                                  !i. i IN u ==> X i x <= z i} =
                      prob p {x | x IN prob_carrier p /\
                                  !i. i IN u ==> Y i x <= z i}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INDEP_RV_FAMILY_ALT; distribution_fn] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(CONJUNCT1 th) THEN
             STRIP_ASSUME_TAC(CONJUNCT1(CONJUNCT2 th)) THEN
             ASSUME_TAC(CONJUNCT2(CONJUNCT2 th))) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:K` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Variables with the same law have the same expectation (integrability      *)
(* transfers); the variance of a sum of pairwise independent square-         *)
(* integrable variables is the sum of the variances; independence is         *)
(* preserved by reindexing along an injection.                               *)
(* ------------------------------------------------------------------------- *)

let EQUIDIST_NONNEG_INTEGRABLE = prove
 (`!p:A prob_space f g.
    integrable p f /\ random_variable p g /\
    (!x. x IN prob_carrier p ==> &0 <= f x) /\
    (!x. x IN prob_carrier p ==> &0 <= g x) /\
    (!a. distribution_fn p f a = distribution_fn p g a)
    ==> integrable p g`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I[integrable] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `expectation p (f:A->real)` THEN
  X_GEN_TAC `h:A->real` THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `M:real` o MATCH_MP SIMPLE_RV_ABS_BOUNDED) THEN
  ABBREV_TAC `c = abs M + &1` THEN SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x. min ((f:A->real) x) c) /\
     integrable p (\x. min ((g:A->real) x) c)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `c:real` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_MIN; RANDOM_VARIABLE_CONST;
                 INTEGRABLE_IMP_RANDOM_VARIABLE; ETA_AX] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier p:A->bool` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= a /\ &0 < c ==> abs(min a c) <= c`];
    ALL_TAC] THEN ASM_SIMP_TAC[GSYM EXPECTATION_SIMPLE_AGREE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x. min ((g:A->real) x) c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN ASM_SIMP_TAC[INTEGRABLE_SIMPLE] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier p:A->bool` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
    DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o
                           check(fun th -> is_forall(concl th) &&
                                   can(find_term((=) `prob_carrier p:A->bool`))
                                   (concl th)))) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `f:A->real`; `g:A->real`; `c:real`]
           EQUIDIST_NONNEG_MIN_EXPECTATION) THEN
  ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EXPECTATION_MONO_AE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `prob_carrier p:A->bool` THEN
  REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let EXPECTATION_EQ_SAME_LAW = prove
 (`!p:A prob_space X Y.
    integrable p X /\ random_variable p Y /\
    (!c. distribution_fn p Y c = distribution_fn p X c)
    ==> integrable p Y /\ expectation p Y = expectation p X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (X:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `Y:A->real`]
           EQUIDIST_MAX_ZERO) THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `Y:A->real`]
           EQUIDIST_NEG_MAX_ZERO) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
    `integrable p (\x. max ((X:A->real) x) (&0)) /\
     integrable p (\x. max (--(X:A->real) x) (&0))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_MAX THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; INTEGRABLE_NEG; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x. max ((Y:A->real) x) (&0)) /\
     integrable p (\x. max (--(Y:A->real) x) (&0))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC EQUIDIST_NONNEG_INTEGRABLE THENL
     [EXISTS_TAC `\x. max ((X:A->real) x) (&0)`;
      EXISTS_TAC `\x. max (--(X:A->real) x) (&0)`] THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_MAX; RANDOM_VARIABLE_CONST;
                 RANDOM_VARIABLE_NEG; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:A->real. Z = \x. max (Z x) (&0) - max (--Z x) (&0)`
    MP_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; EXPECTATION_SUB] THEN BINOP_TAC THEN
  MATCH_MP_TAC EQUIDIST_NONNEG_EXPECTATION THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let VARIANCE_SUM_INDEP_FAMILY = prove
 (`!p:A prob_space (X:K->A->real) s.
    FINITE s /\ kwise_indep_rv_family p 2 s X /\
    (!i. i IN s ==> integrable p (\x. X i x pow 2))
    ==> variance p (\x. sum s (\i. X i x)) = sum s (\i. variance p (X i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i IN s ==> random_variable p ((X:K->A->real) i) /\ integrable p (X i)`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `random_variable p ((X:K->A->real) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
      ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!i j. i IN s /\ j IN s /\ ~(i = j)
           ==> integrable p (\x. (X:K->A->real) i x * X j x) /\
               covariance p (X i) (X j) = &0`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `integrable p (\x. (X:K->A->real) i x * X j x)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COVARIANCE_INDEP THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `i:K`; `j:K`]
             INDEP_RV_FAMILY_PAIR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL[`p:A prob_space`; `2`; `{i:K,j}`; `X:K->A->real`]
             KWISE_INDEP_RV_FAMILY_EQ_INDEP) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    REWRITE_TAC[ARITH_RULE `SUC (SUC 0) <= 2`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_SUBSET THEN EXISTS_TAC `s:K->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. FINITE t
         ==> t SUBSET s
         ==> random_variable p (\x. sum t (\i. (X:K->A->real) i x)) /\
             integrable p (\x. sum t (\i. X i x) pow 2) /\
             variance p (\x. sum t (\i. X i x)) = sum t (\i. variance p (X i))`
    (fun th -> ASM_SIMP_TAC[th; SUBSET_REFL]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES; RANDOM_VARIABLE_CONST; VARIANCE_CONST] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[INTEGRABLE_CONST];
    ALL_TAC] THEN MAP_EVERY X_GEN_TAC[`b:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM SET_TAC[];
    STRIP_TAC] THEN SUBGOAL_THEN `(b:K) IN s` ASSUME_TAC THENL
   [ASM SET_TAC[];
    ALL_TAC] THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
  ABBREV_TAC `S = \x. sum t (\i. (X:K->A->real) i x)` THEN
  SUBGOAL_THEN `!x. sum t (\i. (X:K->A->real) i x) = S x`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[];
    ALL_TAC] THEN RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN
  SUBGOAL_THEN `integrable p (S:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. (S:A->real) x pow 2)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. (X:K->A->real) b x * S x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_MUL_SQUARE THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_ADD THEN ASM_SIMP_TAC[ETA_AX];
    REWRITE_TAC[REAL_ARITH
                  `(a + b:real) pow 2 = a pow 2 + &2 * (a * b) + b pow 2`] THEN
    REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) b`; `S:A->real`]
           VARIANCE_ADD) THEN ASM_SIMP_TAC[ETA_AX] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `c = &0 ==> a + b + &2 * c = a + b`) THEN
  ASM_SIMP_TAC[COVARIANCE_ALT; ETA_AX] THEN EXPAND_TAC "S" THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBGOAL_THEN `!i. i IN t ==> (i:K) IN s /\ ~(b = i)` ASSUME_TAC THENL
   [ASM SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH(lhand o rand) EXPECTATION_SUM_FINITE o lhand o lhand o
      snd) THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `t:K->bool`; `X:K->A->real`]
           EXPECTATION_SUM_FINITE) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_EQ_0 THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(i:K) IN s /\ ~(b = i)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) b`; `(X:K->A->real) i`]
           COVARIANCE_ALT) THEN
  SUBGOAL_THEN
    `integrable p (\x. (X:K->A->real) b x * X i x) /\
     covariance p (X b) (X i) = &0`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_SIMP_TAC[] THEN
  REAL_ARITH_TAC);;

let KWISE_INDEP_RV_FAMILY_REINDEX = prove
 (`!p:A prob_space k (f:K->L) s (X:L->A->real).
    (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
    ==> (kwise_indep_rv_family p k (IMAGE f s) X <=>
         kwise_indep_rv_family p k s (\i. X (f i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[KWISE_INDEP_RV_FAMILY_ALT; FORALL_IN_IMAGE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
  MATCH_MP_TAC(MESON[]
                 `(!u:K->bool. P u ==> (A u <=> B u))
                  ==> ((!u. P u ==> A u) <=> (!u. P u ==> B u))`) THEN
  X_GEN_TAC `u:K->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x y. x IN u /\ y IN u /\ (f:K->L) x = f y ==> x = y`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(IMAGE (f:K->L) u) <=> FINITE u` SUBST1_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `FINITE(u:K->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD(IMAGE (f:K->L) u) = CARD u` SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!g:L->real. product (IMAGE (f:K->L) u) g = product u (\i. g (f i))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL[`f:K->L`; `g:L->real`; `u:K->bool`] PRODUCT_IMAGE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `z:K->real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
                    `\j. (z:K->real) (@i. i IN u /\ (f:K->L) i = j)`) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `!i. i IN u ==> (@i'. i' IN u /\ (f:K->L) i' = f i) = i`
      (fun th -> SIMP_TAC[th]) THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN DISCH_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(@i'. i' IN u /\ (f:K->L) i' = f j) = j`
      (fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `z:L->real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (z:L->real) ((f:K->L) i)`) THEN
    REWRITE_TAC[]]);;

let INDEP_RV_FAMILY_REINDEX = prove
 (`!p:A prob_space (f:K->L) s (X:L->A->real).
    (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
    ==> (indep_rv_family p (IMAGE f s) X <=>
         indep_rv_family p s (\i. X (f i)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INDEP_RV_FAMILY_ALT; FORALL_IN_IMAGE] THEN
  AP_TERM_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
  MATCH_MP_TAC(MESON[]
                 `(!u:K->bool. P u ==> (A u <=> B u))
                  ==> ((!u. P u ==> A u) <=> (!u. P u ==> B u))`) THEN
  X_GEN_TAC `u:K->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x y. x IN u /\ y IN u /\ (f:K->L) x = f y ==> x = y`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(IMAGE (f:K->L) u) <=> FINITE u` SUBST1_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `FINITE(u:K->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `!g:L->real. product (IMAGE (f:K->L) u) g = product u (\i. g (f i))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL[`f:K->L`; `g:L->real`; `u:K->bool`] PRODUCT_IMAGE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `z:K->real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
                    `\j. (z:K->real) (@i. i IN u /\ (f:K->L) i = j)`) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `!i. i IN u ==> (@i'. i' IN u /\ (f:K->L) i' = f i) = i`
      (fun th -> SIMP_TAC[th]) THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN DISCH_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(@i'. i' IN u /\ (f:K->L) i' = f j) = j`
      (fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `z:L->real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (z:L->real) ((f:K->L) i)`) THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Chernoff 2, equality of the tails: for independent symmetric X_i, Pr[sum  *)
(* X_i >= d] = Pr[sum X_i <= -d], for any d.                                 *)
(* ------------------------------------------------------------------------- *)

let CHERNOFF_SYMMETRIC_TAILS_EQ = prove
 (`!p:A prob_space (X:K->A->real) s d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i c. i IN s
           ==> distribution_fn p (\x. --X i x) c = distribution_fn p (X i) c)
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= d} =
        prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) <= --d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `indep_rv_family p s (\i x. --(X:K->A->real) i x)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\t:real. --t`]
             MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ON_NEG; REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `\i x. --(X:K->A->real) i x`;
                `s:K->bool`] JOINT_LAW_EQ_BOXES) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RANDOM_VARIABLE_NEG THEN
      ASM_SIMP_TAC[ETA_AX];
      MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`;
                    `\i x. --(X:K->A->real) i x`; `s:K->bool`]
               INDEP_RV_FAMILY_JOINT_CDF) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN DISCH_THEN(MP_TAC o SPEC `{y:K->real | sum s y >= d}`) THEN
  ASM_SIMP_TAC[BOX_SIGMA_ALGEBRA_SUM_GE; IN_ELIM_THM; SUM_NEG] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge;
              REAL_ARITH `d <= --s <=> s <= --d`]);;

(* ------------------------------------------------------------------------- *)
(* Exponential moments: the Chernoff bound Pr[X >= t] <= exp(-l t) E[exp(l   *)
(* X)] for l >= 0, the exponential moment of a sum of independent variables  *)
(* bounded above, and Hoeffding's lemma E[exp(l X)] <= exp(l^2 (b - a)^2 /   *)
(* 8) for E X = 0 and a <= X <= b, any real l.                               *)
(* ------------------------------------------------------------------------- *)

let REAL_CONTINUOUS_ON_EXP_LMUL = prove
 (`!l s. (\t. exp(l * t)) real_continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\t. exp(l * t)) = exp o (\t. l * t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID;
             REAL_CONTINUOUS_ON_EXP]]);;

let RANDOM_VARIABLE_EXP_CMUL = prove
 (`!p:A prob_space X l.
        random_variable p X ==> random_variable p (\x. exp(l * X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `\t. exp(l * t)`]
           RANDOM_VARIABLE_COMP_CONTINUOUS) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_EXP_LMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CHERNOFF_EXPECTATION_BOUND = prove
 (`!p:A prob_space X l t.
        random_variable p X /\ &0 <= l /\ integrable p (\x. exp(l * X x))
        ==> prob p {x | x IN prob_carrier p /\ X x >= t} <=
            exp(--(l * t)) * expectation p (\x. exp(l * X x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `\y. exp(l * y)`;
                `{y:real | y >= t}`; `exp(l * t)`] MARKOV_SET_INEQUALITY) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_EXP_POS_LT] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; REAL_EXP_POS_LE];
      REWRITE_TAC[real_ge; REAL_EXP_MONO_LE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RV_PREIMAGE_GE THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[real_div; REAL_MUL_SYM; GSYM REAL_EXP_NEG]]);;

let PROB_ABS_GE_LE_ADD = prove
 (`!p:A prob_space Y d.
        random_variable p Y
        ==> prob p {x | x IN prob_carrier p /\ abs(Y x) >= d} <=
            prob p {x | x IN prob_carrier p /\ Y x >= d} +
            prob p {x | x IN prob_carrier p /\ --Y x >= d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier p /\ abs((Y:A->real) x) >= d} =
     {x | x IN prob_carrier p /\ Y x >= d} UNION
     {x | x IN prob_carrier p /\ --Y x >= d}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `x IN prob_carrier (p:A prob_space)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PROB_SUBADDITIVE THEN
    ASM_SIMP_TAC[RV_PREIMAGE_GE; RANDOM_VARIABLE_NEG]]);;

let EXPECTATION_EXP_SUM_INDEP = prove
 (`!p:A prob_space (X:K->A->real) s l M.
        FINITE s /\ indep_rv_family p s X /\ &0 <= l /\
        (!i. i IN s ==> almost_surely p {x | X i x <= M i})
        ==> integrable p (\x. exp(l * sum s (\i. X i x))) /\
            expectation p (\x. exp(l * sum s (\i. X i x))) =
            product s (\i. expectation p (\x. exp(l * X i x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; REAL_EXP_SUM] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `\i:K t. exp(l * t)`;
                `s:K->bool`]
           INDEP_RV_FAMILY_EXPECTATION_PRODUCT_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EXP_LMUL];
    EXISTS_TAC `exp(l * (M:K->real) i)` THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:K->A->real) i x <= M i}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_EXP; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let EXP_LMUL_LE_ENDPOINTS = prove
 (`!l a b x. a <= x /\ x <= b ==> exp(l * x) <= exp(l * a) + exp(l * b)`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= l \/ l <= &0`) THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= b /\ &0 < a ==> x <= a + b`) THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `x <= a /\ &0 < b ==> x <= a + b`) THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `l * a <= l * x <=> --l * x <= --l * a`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let HOEFFDING_LEMMA_EXPECTATION = prove
 (`!p:A prob_space X a b l.
    random_variable p X /\ expectation p X = &0 /\
    almost_surely p {x | a <= X x /\ X x <= b}
    ==> integrable p (\x. exp(l * X x)) /\
        expectation p (\x. exp(l * X x)) <= exp(l pow 2 * (b - a) pow 2 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `abs a + abs b` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `a <= &0 /\ &0 <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL[`p:A prob_space`; `\x:A. a:real`; `X:A->real`]
               EXPECTATION_MONO_AE);
      MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `\x:A. b:real`]
               EXPECTATION_MONO_AE)] THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. exp(l * (X:A->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `exp(l * a) + exp(l * b)` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_EXP_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ABS_EXP; EXP_LMUL_LE_ENDPOINTS];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `a:real = b` THENL
   [SUBGOAL_THEN `a = &0 /\ b = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `\x:A. &1`; `\x. exp(l * (X:A->real) x)`]
             EXPECTATION_AS_EQ) THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST;
                 RANDOM_VARIABLE_EXP_CMUL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(X:A->real) x = &0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO; REAL_EXP_0]];
      STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_MUL_LZERO; REAL_EXP_0;
                  REAL_LE_REFL]];
    ALL_TAC] THEN SUBGOAL_THEN `(a:real) < b` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `b / (b - a) * exp(l * a) + (--a) / (b - a) * exp(l * b)` THEN
  ASM_SIMP_TAC[HOEFFDING_ANALYTIC_LEMMA] THEN
  ABBREV_TAC `c = (b * exp(l * a) - a * exp(l * b)) / (b - a)` THEN
  ABBREV_TAC `d = (exp(l * b) - exp(l * a)) / (b - a)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. c + d * (X:A->real) x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `(b - (X:A->real) x) / (b - a) * exp(l * a) +
       (X x - a) / (b - a) * exp(l * b)` THEN
    ASM_SIMP_TAC[CONVEX_BOUND_EXP] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MAP_EVERY EXPAND_TAC["c"; "d"] THEN UNDISCH_TAC `(a:real) < b` THEN
    CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL;
                 EXPECTATION_CMUL; EXPECTATION_CONST] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "c" THEN
    UNDISCH_TAC `(a:real) < b` THEN CONV_TAC REAL_FIELD]);;

let HOEFFDING_LEMMA_CENTRED = prove
 (`!p:A prob_space X a b l.
    random_variable p X /\ almost_surely p {x | a <= X x /\ X x <= b}
    ==> expectation p (\x. exp(l * (X x - expectation p X))) <=
        exp(l pow 2 * (b - a) pow 2 / &8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `abs a + abs b` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\x. (X:A->real) x - expectation p X`;
                `a - expectation p (X:A->real)`;
                `b - expectation p (X:A->real)`; `l:real`]
           HOEFFDING_LEMMA_EXPECTATION) THEN
  REWRITE_TAC[REAL_ARITH `(b - m) - (a - m) = b - a:real`] THEN ANTS_TAC THENL
   [ALL_TAC;
    SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_REWRITE_TAC[RANDOM_VARIABLE_CONST];
    ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | a <= (X:A->real) x /\ X x <= b}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hoeffding's inequality, one-sided and two-sided.                          *)
(* ------------------------------------------------------------------------- *)

let HOEFFDING_INEQUALITY_UPPER = prove
 (`!p:A prob_space (X:K->A->real) s a b d.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | a i <= X i x /\ X i x <= b i}) /\
    &0 <= d
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x) - sum s (\i. expectation p (X i)) >= d}
        <= exp(--(&2 * d pow 2) / sum s (\i. (b i - a i) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `abs((a:K->real) i) + abs((b:K->real) i)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (a:K->real) i <= (X:K->A->real) i x /\ X i x <= b i}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  ABBREV_TAC `Y = \i x. (X:K->A->real) i x - expectation p (X i)` THEN
  SUBGOAL_THEN
    `!x. sum s (\i. (X:K->A->real) i x - expectation p (X i)) =
         sum s (\i. Y i x)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[];
    ALL_TAC] THEN ABBREV_TAC `D = sum s (\i. ((b:K->real) i - a i) pow 2)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((Y:K->A->real) i)`
    ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier p /\ sum s (\i. (Y:K->A->real) i x) >= d} IN
     prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `D = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_EXP_0] THEN
    ASM_SIMP_TAC[PROB_LE_1];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `indep_rv_family p s (Y:K->A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    EXPAND_TAC "Y" THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`;
                  `\t. t - expectation p ((X:K->A->real) i)`]
             MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
                 REAL_CONTINUOUS_ON_CONST];
    ALL_TAC] THEN ABBREV_TAC `l = &4 * d / D` THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `Y:K->A->real`; `s:K->bool`; `l:real`;
                `\i. (b:K->real) i - expectation p ((X:K->A->real) i)`]
           EXPECTATION_EXP_SUM_INDEP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (a:K->real) i <= (X:K->A->real) i x /\ X i x <= b i}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN EXPAND_TAC "Y" THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(l * d)) *
     expectation p (\x. exp(l * sum s (\i. (Y:K->A->real) i x)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `\x. sum s (\i. (Y:K->A->real) i x)`;
                  `l:real`; `d:real`] CHERNOFF_EXPECTATION_BOUND) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUM_FINITE];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `!i. i IN s
         ==> integrable p (\x. exp(l * (Y:K->A->real) i x)) /\
             expectation p (\x. exp(l * Y i x))
             <= exp(l pow 2 * ((b:K->real) i - a i) pow 2 / &8)`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(Y:K->A->real) i`;
                  `(a:K->real) i - expectation p ((X:K->A->real) i)`;
                  `(b:K->real) i - expectation p ((X:K->A->real) i)`; `l:real`]
             HOEFFDING_LEMMA_EXPECTATION) THEN
    REWRITE_TAC[REAL_ARITH `(b - m) - (a - m) = b - a:real`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Y" THEN
      ASM_SIMP_TAC[EXPECTATION_SUB; INTEGRABLE_CONST; EXPECTATION_CONST;
                   ETA_AX] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC
        `{x | (a:K->real) i <= (X:K->A->real) i x /\ X i x <= b i}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM] THEN EXPAND_TAC "Y" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(l * d)) *
     product s (\i. exp(l pow 2 * ((b:K->real) i - a i) pow 2 / &8))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EXPECTATION_POS THEN ASM_SIMP_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_EXP_SUM; GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  REWRITE_TAC[real_div; SUM_LMUL; SUM_RMUL] THEN
  ASM_REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  EXPAND_TAC "l" THEN UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD);;

let HOEFFDING_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s a b d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | a i <= X i x /\ X i x <= b i}) /\
    &0 <= d
    ==> prob p {x | x IN prob_carrier p /\
                    abs(sum s (\i. X i x) - sum s (\i. expectation p (X i)))
                    >= d}
        <= &2 * exp(--(&2 * d pow 2) / sum s (\i. (b i - a i) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`;
                `\x. sum s (\i. (X:K->A->real) i x) -
                     sum s (\i. expectation p (X i))`;
                `d:real`] PROB_ABS_GE_LE_ADD) THEN
  ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_SUM_FINITE;
               RANDOM_VARIABLE_CONST] THEN
  MATCH_MP_TAC(REAL_ARITH
                 `a <= e /\ b <= e ==> x <= a + b ==> x <= &2 * e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOEFFDING_INEQUALITY_UPPER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\i x. --(X:K->A->real) i x`; `s:K->bool`;
                `\i. --(b:K->real) i`; `\i. --(a:K->real) i`; `d:real`]
           HOEFFDING_INEQUALITY_UPPER) THEN
  REWRITE_TAC[REAL_ARITH `--a - --b = b - a:real`] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_NEG2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\t:real. --t`]
               MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_NEG; REAL_CONTINUOUS_ON_ID];
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `sum s (\i. expectation p (\x. --(X:K->A->real) i x)) =
     sum s (\i. --expectation p (X i))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) j`] EXPECTATION_NEG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_NEG; REAL_ARITH `--a - --b = --(a - b:real)`]);;

(* ------------------------------------------------------------------------- *)
(* Chernoff 2: each tail of a sum of n independent centred variables with    *)
(* |X_i| <= 1 is at most exp(-d^2 / (2n)).                                   *)
(* ------------------------------------------------------------------------- *)

let CHERNOFF_SYMMETRIC_UPPER_LEMMA = prove
 (`!p:A prob_space (X:K->A->real) s d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> expectation p (X i) = &0 /\
                    almost_surely p {x | abs(X i x) <= &1}) /\
    &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= d}
          <= exp(--(d pow 2) / (&2 * &(CARD s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `\i:K. --(&1)`;
                `\i:K. &1`; `d:real`] HOEFFDING_INEQUALITY_UPPER) THEN
  ASM_SIMP_TAC[SUM_CONST; SUM_0] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:K->A->real) i x) <= &1}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum s (\i:K. expectation p ((X:K->A->real) i)) = &0`
    SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN
    `--(&2 * d pow 2) / (&(CARD(s:K->bool)) * &4) =
     --(d pow 2) / (&2 * &(CARD s))`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `&(CARD(s:K->bool)) = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; real_div; REAL_INV_0];
    UNDISCH_TAC `~(&(CARD(s:K->bool)) = &0)` THEN CONV_TAC REAL_FIELD]);;

let CHERNOFF_SYMMETRIC_TAILS = prove
 (`!p:A prob_space (X:K->A->real) s d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> expectation p (X i) = &0 /\
                    almost_surely p {x | abs(X i x) <= &1}) /\
    &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= d}
          <= exp(--(d pow 2) / (&2 * &(CARD s))) /\
        prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) <= --d}
          <= exp(--(d pow 2) / (&2 * &(CARD s)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CHERNOFF_SYMMETRIC_UPPER_LEMMA THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\i x. --(X:K->A->real) i x`; `s:K->bool`;
                `d:real`] CHERNOFF_SYMMETRIC_UPPER_LEMMA) THEN
  ASM_SIMP_TAC[EXPECTATION_NEG; REAL_ABS_NEG; REAL_NEG_0; SUM_NEG] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\t:real. --t`]
               MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_NEG; REAL_CONTINUOUS_ON_ID];
      X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) j`] EXPECTATION_NEG) THEN
      ASM_SIMP_TAC[REAL_NEG_0]];
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= e ==> b <= e`) THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge;
                REAL_ARITH `d <= --s <=> s <= --d`]]);;

(* ------------------------------------------------------------------------- *)
(* Chernoff 3, 4 and 5: multiplicative bounds for sums of independent        *)
(* variables in [0,1] with mu = sum E X_i.                                   *)
(* ------------------------------------------------------------------------- *)

let EXP_DIV_RPOW_RPOW = prove
 (`!a b m. &0 < b ==> (exp a / b rpow b) rpow m = exp(m * (a - b * log b))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rpow] THEN
  REWRITE_TAC[GSYM REAL_EXP_SUB; REAL_EXP_POS_LT; LOG_EXP]);;

let EXPECTATION_UNIT_BOUNDS = prove
 (`!p:A prob_space X.
        random_variable p X /\ almost_surely p {x | &0 <= X x /\ X x <= &1}
        ==> integrable p X /\ &0 <= expectation p X /\ expectation p X <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `\x:A. &0`; `X:A->real`]
             EXPECTATION_MONO_AE);
    MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `\x:A. &1`]
             EXPECTATION_MONO_AE)] THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let EXPECTATION_EXP_UNIT_LE = prove
 (`!p:A prob_space X l.
        random_variable p X /\ almost_surely p {x | &0 <= X x /\ X x <= &1}
        ==> integrable p (\x. exp(l * X x)) /\
            expectation p (\x. exp(l * X x)) <=
            exp(expectation p X * (exp l - &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. exp(l * (X:A->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `exp(l * &0) + exp(l * &1)` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_EXP_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ABS_EXP; EXP_LMUL_LE_ENDPOINTS];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x. &1 + (exp l - &1) * (X:A->real) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`l:real`; `&0`; `&1`; `(X:A->real) x`] CONVEX_BOUND_EXP) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL;
                 EXPECTATION_CMUL; EXPECTATION_CONST] THEN
    MP_TAC(SPEC `expectation p (X:A->real) * (exp l - &1)` REAL_EXP_LE_X) THEN
    REAL_ARITH_TAC]);;

let CHERNOFF_UNIT_MGF_SUM = prove
 (`!p:A prob_space (X:K->A->real) s l.
        FINITE s /\ indep_rv_family p s X /\
        (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1})
        ==> integrable p (\x. exp(l * sum s (\i. X i x))) /\
            expectation p (\x. exp(l * sum s (\i. X i x))) <=
            exp(sum s (\i. expectation p (X i)) * (exp l - &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN ASM_SIMP_TAC[GSYM SUM_LMUL; REAL_EXP_SUM] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `\i:K t. exp(l * t)`;
                `s:K->bool`]
           INDEP_RV_FAMILY_EXPECTATION_PRODUCT_CONTINUOUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_EXP_LMUL] THEN X_GEN_TAC `i:K` THEN
    DISCH_TAC THEN EXISTS_TAC `exp(l * &0) + exp(l * &1)` THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:K->A->real) i x /\ X i x <= &1}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ABS_EXP; EXP_LMUL_LE_ENDPOINTS];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM SUM_RMUL; REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `l:real`]
           EXPECTATION_EXP_UNIT_LE) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

let CHERNOFF_UNIT_UPPER_EXP = prove
 (`!p:A prob_space (X:K->A->real) s r t.
        FINITE s /\ indep_rv_family p s X /\
        (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
        &0 <= t
        ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= r} <=
            exp(--(t * r) + sum s (\i. expectation p (X i)) * (exp t - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `t:real`]
           CHERNOFF_UNIT_MGF_SUM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(t * r)) *
     expectation p (\x. exp(t * sum s (\i. (X:K->A->real) i x)))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `\x. sum s (\i. (X:K->A->real) i x)`;
                  `t:real`; `r:real`] CHERNOFF_EXPECTATION_BOUND) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUM_FINITE];
    REWRITE_TAC[REAL_EXP_ADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

let CHERNOFF_UNIT_LOWER_EXP = prove
 (`!p:A prob_space (X:K->A->real) s r t.
        FINITE s /\ indep_rv_family p s X /\
        (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
        &0 <= t
        ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) <= r} <=
            exp(t * r + sum s (\i. expectation p (X i)) * (exp(--t) - &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `--t:real`]
           CHERNOFF_UNIT_MGF_SUM) THEN REWRITE_TAC[REAL_MUL_LNEG] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(t * r) *
     expectation p (\x. exp(--(t * sum s (\i. (X:K->A->real) i x))))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `\x. --sum s (\i. (X:K->A->real) i x)`;
                  `t:real`; `--r:real`] CHERNOFF_EXPECTATION_BOUND) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUM_FINITE; RANDOM_VARIABLE_NEG] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> a <= e ==> b <= e`) THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_ge; REAL_LE_NEG2];
    REWRITE_TAC[REAL_EXP_ADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

let CHERNOFF_UPPER_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s mu d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    mu = sum s (\i. expectation p (X i)) /\ &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= (&1 + d) * mu}
          <= (exp d / (&1 + d) rpow (&1 + d)) rpow mu /\
        (exp d / (&1 + d) rpow (&1 + d)) rpow mu <=
        exp(--(mu * d pow 2) / (&2 + d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
             EXPECTATION_UNIT_BOUNDS) THEN ANTS_TAC THENL
     [ALL_TAC;
      SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXP_DIV_RPOW_RPOW; REAL_ARITH `&0 <= d ==> &0 < &1 + d`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`;
                  `(&1 + d) * mu`; `log(&1 + d)`] CHERNOFF_UNIT_UPPER_EXP) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_ARITH `&0 <= d ==> &1 <= &1 + d`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&0 <= d ==> &0 < &1 + d`] THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> x <= a ==> x <= b`) THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN UNDISCH_TAC `&0 <= mu` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = sum s (\i. expectation p ((X:K->A->real) i))` THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `d:real` LOG_GE_DIV_HALF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `m * (d - (&1 + d) * (&2 * d / (&2 + d)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `(b:real) <= a ==> d - a <= d - b`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 <= d` THEN
    CONV_TAC REAL_FIELD]);;

let EXP_LE_QUADRATIC_NONPOS = prove
 (`!x. x <= &0 ==> exp x <= &1 + x + x pow 2 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`1`; `x:real`] REAL_EXP_LE_PARTIAL_SUM_EVEN) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * 1 = 2`; num_CONV `2`; num_CONV `1`;
                  SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[LE_0; FACT; real_pow] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let CHERNOFF_LOWER_EXPONENT_LE = prove
 (`!d. &0 <= d /\ d <= &1
       ==> --d - (&1 - d) * log(&1 - d) <= --(d pow 2) / &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = &1` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`\y. --(y pow 2) / &2`; `\y. --y - (&1 - y) * log(&1 - y)`;
                `\y:real. --y`; `\y. log(&1 - y)`; `{y | &0 <= y /\ y < &1}`;
                `&0`; `d:real`] HAS_REAL_DERIVATIVE_LE_IMP_LE) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN SUBGOAL_THEN `(&1 - y) * inv(&1 - y) = &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN CONV_TAC REAL_RING;
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `--y:real` LOG_LE_STRONG) THEN
    REWRITE_TAC[GSYM real_sub] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_RZERO; LOG_1] THEN REAL_ARITH_TAC]);;

let CHERNOFF_LOWER_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s mu d.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    mu = sum s (\i. expectation p (X i)) /\ &0 <= d /\ d <= &1
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) <= (&1 - d) * mu}
          <= (exp(--d) / (&1 - d) rpow (&1 - d)) rpow mu /\
        (exp(--d) / (&1 - d) rpow (&1 - d)) rpow mu <=
        exp(--(mu * d pow 2) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
             EXPECTATION_UNIT_BOUNDS) THEN ANTS_TAC THENL
     [ALL_TAC;
      SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `d = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(exp(--(&1)) / (&1 - &1) rpow (&1 - &1)) rpow mu = exp(--mu)`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; RPOW_ZERO; REAL_DIV_1] THEN
      REWRITE_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `\n. exp(mu * (inv(&n) - &1))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `exp(--mu) = exp(mu * (&0 - &1))` SUBST1_TAC THENL
       [AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_EXP] THEN MATCH_MP_TAC REALLIM_LMUL THEN
      MATCH_MP_TAC REALLIM_SUB THEN
      REWRITE_TAC[REALLIM_1_OVER_N; REALLIM_CONST];
      ALL_TAC] THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `&0`;
                  `log(&n)`] CHERNOFF_UNIT_LOWER_EXP) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
    ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG; REAL_OF_NUM_LT;
                 ARITH_RULE `1 <= n ==> 0 < n`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `log(&1 - d) <= &0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV[GSYM LOG_1] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_SIMP_TAC[EXP_DIV_RPOW_RPOW] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`;
                  `(&1 - d) * mu`; `--log(&1 - d)`]
             CHERNOFF_UNIT_LOWER_EXP) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
    MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> x <= a ==> x <= b`) THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= mu` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `m = sum s (\i. expectation p ((X:K->A->real) i))` THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MP_TAC(SPEC `d:real` CHERNOFF_LOWER_EXPONENT_LE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `m * (--(d pow 2) / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

let CHERNOFF_LOWER_INEQUALITY_GEN = prove
 (`!p:A prob_space (X:K->A->real) s mu d.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    mu = sum s (\i. expectation p (X i)) /\ &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) <= (&1 - d) * mu}
        <= exp(--(mu * d pow 2) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
             EXPECTATION_UNIT_BOUNDS) THEN ANTS_TAC THENL
     [ALL_TAC;
      SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `(&1 - d) * mu`;
                `d:real`] CHERNOFF_UNIT_LOWER_EXP) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `--d:real` EXP_LE_QUADRATIC_NONPOS) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
                `&1 + --d + (--d) pow 2 / &2 = &1 - d + d pow 2 / &2`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mu * exp(--d) <= mu * (&1 - d + d pow 2 / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN REAL_ARITH_TAC);;

let CHERNOFF_FAR_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s mu r.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    mu = sum s (\i. expectation p (X i)) /\ &2 * exp(&1) * mu <= r
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= r} <=
        &2 rpow --r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= mu` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
             EXPECTATION_UNIT_BOUNDS) THEN ANTS_TAC THENL
     [ALL_TAC;
      SIMP_TAC[]] THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `r:real`;
                `&1 + log(&2)`] CHERNOFF_UNIT_UPPER_EXP) THEN
  ASM_SIMP_TAC[LOG_POS; REAL_ARITH `&1 <= &2`;
               REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SIMP_TAC[REAL_EXP_ADD; EXP_LOG; REAL_ARITH `&0 < &2`] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bennett's and Bernstein's inequalities in the general form: raw second    *)
(* moments V = sum E[X_i^2], the centred sum, a one-sided bound X_i <= M for *)
(* any real M; and the sheet's forms (mean zero, sigma^2 = sum Var X_i / n)  *)
(* as corollaries.                                                           *)
(* ------------------------------------------------------------------------- *)

let EXP_CUBIC_AUX_SIGN = prove
 (`!y. (&0 <= y ==> &0 <= (y - &2) * exp y + y + &2) /\
       (y <= &0 ==> (y - &2) * exp y + y + &2 <= &0)`,
  SUBGOAL_THEN
    `!a b. a <= b ==> (a - &2) * exp a + a + &2 <= (b - &2) * exp b + b + &2`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`\y. (y - &2) * exp y + y + &2`; `\y. (y - &1) * exp y + &1`;
                  `(:real)`; `a:real`; `b:real`]
             HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_UNIV; IS_REALINTERVAL_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN
      SUBGOAL_THEN `exp y * (&1 + --y) <= exp y * exp(--y)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_LE_X];
        REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL[`&0`; `y:real`]);
    FIRST_X_ASSUM(MP_TAC o SPECL[`y:real`; `&0`])] THEN
  ASM_REWRITE_TAC[REAL_EXP_0] THEN REAL_ARITH_TAC);;

let REAL_DIV_NEG_NEG = prove
 (`!x y:real. x / y = (--x) / (--y)`,
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_NEG_MUL2]);;

let EXP_QUAD_RATIO_MONO_SIDE = prove
 (`!a b. (&0 < a /\ a <= b) \/ (a <= b /\ b < &0)
         ==> (exp a - &1 - a) / a pow 2 <= (exp b - &1 - b) / b pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL[`\y. (exp y - &1 - y) / y pow 2`;
                  `\y. ((y - &2) * exp y + y + &2) / y pow 3`; `{y | &0 < y}`;
                  `a:real`; `b:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP);
    MP_TAC(ISPECL[`\y. (exp y - &1 - y) / y pow 2`;
                  `\y. ((y - &2) * exp y + y + &2) / y pow 3`; `{y | y < &0}`;
                  `a:real`; `b:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (CONJ_TAC THENL
    [X_GEN_TAC `y:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN SUBGOAL_THEN `~(y = &0)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD;
     ALL_TAC]) THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[EXP_CUBIC_AUX_SIGN; REAL_LT_IMP_LE; REAL_POW_LE];
    ONCE_REWRITE_TAC[REAL_DIV_NEG_NEG] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_NEG_GE0] THEN
      MATCH_MP_TAC(CONJUNCT2(SPEC `y:real` EXP_CUBIC_AUX_SIGN)) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_RING `--((y:real) pow 3) = (--y) pow 3`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]);;

let EXP_GE_QUADRATIC_NONNEG = prove
 (`!x. &0 <= x ==> &1 + x + x pow 2 / &2 <= exp x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`2`; `1`; `x:real`] REAL_EXP_GE_PARTIAL_SUM_POW) THEN
  ASM_REWRITE_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[LE_0; FACT; real_pow; REAL_POW_1; REAL_DIV_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let EXP_QUAD_RATIO_MONO = prove
 (`!a b. ~(a = &0) /\ ~(b = &0) /\ a <= b
         ==> (exp a - &1 - a) / a pow 2 <= (exp b - &1 - b) / b pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < a` THENL
   [MATCH_MP_TAC EXP_QUAD_RATIO_MONO_SIDE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_CASES_TAC `b < &0` THENL
   [MATCH_MP_TAC EXP_QUAD_RATIO_MONO_SIDE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2` THEN
  SUBGOAL_THEN `&0 < a pow 2 /\ &0 < b pow 2` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2];
    ALL_TAC] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `a:real` EXP_LE_QUADRATIC_NONPOS) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPEC `b:real` EXP_GE_QUADRATIC_NONNEG) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let BENNETT_EXP_LE = prove
 (`!l M x. &0 <= l /\ ~(M = &0) /\ x <= M
           ==> exp(l * x) <=
               &1 + l * x + x pow 2 * (exp(l * M) - &1 - l * M) / M pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `l = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO;
                REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_EXP_0] THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`(l:real) * x`; `(l:real) * M`] EXP_QUAD_RATIO_MONO) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < ((l:real) * x) pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2; REAL_ENTIRE];
    ALL_TAC] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
                 `a = b ==> e - &1 - lx <= a ==> e <= &1 + lx + b`) THEN
  UNDISCH_TAC `~(l = &0)` THEN UNDISCH_TAC `~(M = &0)` THEN
  CONV_TAC REAL_FIELD);;

let EXPECTATION_POW2_GE = prove
 (`!p:A prob_space X.
        random_variable p X /\ integrable p (\x. X x pow 2)
        ==> expectation p X pow 2 <= expectation p (\x. X x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_POW2_IMP];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`] VARIANCE_ALT) THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`] VARIANCE_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
    `(\x. ((X:A->real) x - expectation p X) pow 2) =
     (\x. X x pow 2 + --(&2 * expectation p X) * X x + expectation p X pow 2)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_CONST]);;

let ALMOST_SURELY_FINITE_FORALL = prove
 (`!p:A prob_space (P:K->A->bool) s.
        FINITE s /\ (!i. i IN s ==> almost_surely p (P i))
        ==> almost_surely p {x | !i. i IN s ==> x IN P i}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
    REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM];
    ALL_TAC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `(P:K->A->bool) x INTER {y | !i. i IN s ==> y IN P i}` THEN
  ASM_SIMP_TAC[ALMOST_SURELY_INTER] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[]);;

let PROB_ZERO_OUTSIDE_ALMOST_SURELY = prove
 (`!p:A prob_space Q a.
        almost_surely p Q /\ a IN prob_events p /\
        (!x. x IN a ==> ~(x IN Q))
        ==> prob p a = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[almost_surely; null_event] THEN
  DISCH_THEN(CONJUNCTS_THEN2(X_CHOOSE_THEN `n:A->bool` STRIP_ASSUME_TAC)
               STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  ASM_SIMP_TAC[PROB_POSITIVE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check(is_eq o concl)) THEN
  MATCH_MP_TAC PROB_MONO THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PROB_EVENT_SUBSET o
                check(fun th -> rand(concl th) = `prob_events (p:A prob_space)`
                        && lhand(concl th) = `a:A->bool`)) THEN
  ASM SET_TAC[]);;

let BENNETT_MGF_CENTRED = prove
 (`!p:A prob_space X M l.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        almost_surely p {x | X x <= M} /\ ~(M = &0) /\ &0 <= l
        ==> integrable p (\x. exp(l * (X x - expectation p X))) /\
            expectation p (\x. exp(l * (X x - expectation p X))) <=
            exp(expectation p (\x. X x pow 2) *
                (exp(l * M) - &1 - l * M) / M pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_POW2_IMP];
    ALL_TAC] THEN ABBREV_TAC `m = expectation p (X:A->real)` THEN
  ABBREV_TAC `c = (exp(l * M) - &1 - l * M) / M pow 2` THEN
  SUBGOAL_THEN `integrable p (\x. exp(l * (X:A->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `exp(l * M)` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_EXP_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:A->real) x <= M}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ABS_EXP; REAL_EXP_MONO_LE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. exp(l * ((X:A->real) x - m))) = (\x. exp(--(l * m)) * exp(l * X x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_EXP_ADD] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(l * m)) *
     exp(l * m + expectation p (\x. (X:A->real) x pow 2) * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `expectation p (\x. &1 + l * (X:A->real) x + c * X x pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
      ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL] THEN
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | (X:A->real) x <= M}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL[`l:real`; `M:real`; `(X:A->real) x`] BENNETT_EXP_LE) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_ADD; INTEGRABLE_CONST;
                   INTEGRABLE_CMUL; EXPECTATION_CMUL; EXPECTATION_CONST] THEN
      MP_TAC(SPEC `l * m + expectation p (\x. (X:A->real) x pow 2) * c`
               REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC]);;

let BENNETT_INEQUALITY_GEN = prove
 (`!p:A prob_space (X:K->A->real) s M e.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> integrable p (\x. X i x pow 2) /\
                    almost_surely p {x | X i x <= M}) /\ &0 <= e
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x - expectation p (X i)) >= e} <=
        exp(--(sum s (\i. expectation p (\x. X i x pow 2)) / M pow 2) *
            ((&1 + M * e / sum s (\i. expectation p (\x. X i x pow 2))) *
             log(&1 + M * e / sum s (\i. expectation p (\x. X i x pow 2))) -
             M * e / sum s (\i. expectation p (\x. X i x pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
    `V = sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2))` THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EXPECTATION_POS THEN
    ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier p /\
      sum s (\i. (X:K->A->real) i x - expectation p (X i)) >= e} IN
     prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MP_TAC(ISPECL[`p:A prob_space`;
                  `\i x. (X:K->A->real) i x - expectation p (X i)`;
                  `s:K->bool`] RANDOM_VARIABLE_SUM_FINITE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST; ETA_AX];
    ALL_TAC] THEN ASM_CASES_TAC `M = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; real_div; REAL_INV_0;
                    REAL_MUL_RZERO; REAL_NEG_0; REAL_MUL_LZERO;
                    REAL_EXP_0] THEN ASM_SIMP_TAC[PROB_LE_1];
    ALL_TAC] THEN ASM_CASES_TAC `V = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO;
                    REAL_NEG_0; REAL_EXP_0] THEN ASM_SIMP_TAC[PROB_LE_1];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < V` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ABBREV_TAC `u = (M:real) * e / V` THEN
  SUBGOAL_THEN `!i. i IN s ==> expectation p ((X:K->A->real) i) <= M`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\x:A. M:real`]
             EXPECTATION_MONO_AE) THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; ETA_AX];
    ALL_TAC] THEN ASM_CASES_TAC `u <= -- &1` THENL
   [MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= y`) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC PROB_ZERO_OUTSIDE_ALMOST_SURELY THEN
    EXISTS_TAC `{x | !i. i IN s ==> x IN {y | (X:K->A->real) i y <= M}}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_FINITE_FORALL] THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    ASM_CASES_TAC `!i. i IN s ==> (X:K->A->real) i x <= M` THENL
     [ALL_TAC;
      ASM_MESON_TAC[]] THEN SUBGOAL_THEN `M < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= u` MP_TAC THENL
       [EXPAND_TAC "u" THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC
      `e <= sum s (\i. (X:K->A->real) i x - expectation p (X i))` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ONCE_REWRITE_TAC[TAUT `~a ==> b <=> ~b ==> a`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(s:K->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
        `sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2)) = V` THEN
      ASM_REWRITE_TAC[SUM_CLAUSES] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum s (\i. M - expectation p ((X:K->A->real) i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[REAL_ARITH `(a:real) <= b ==> a - c <= b - c`];
      ALL_TAC] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC
      `sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2) / --M)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LT_ALL THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN
      DISCH_TAC THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `M < &0 ==> &0 < --M`] THEN
      MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
               EXPECTATION_POW2_GE) THEN ASM_SIMP_TAC[] THEN
      ABBREV_TAC `m = expectation p ((X:K->A->real) i)` THEN
      MP_TAC(SPEC `M:real` REAL_LT_POW_2) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `m - M / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `M < &0 ==> &0 < --M`] THEN
      UNDISCH_TAC `u <= -- &1` THEN EXPAND_TAC "u" THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < &1 + u` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `&0 <= log(&1 + u) / M` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < M` THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC LOG_POS THEN SUBGOAL_THEN `&0 <= u` MP_TAC THENL
       [EXPAND_TAC "u" THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      ONCE_REWRITE_TAC[REAL_DIV_NEG_NEG] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_NEG_GE0] THEN GEN_REWRITE_TAC RAND_CONV[GSYM LOG_1] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `u <= &0` MP_TAC THENL
       [EXPAND_TAC "u" THEN
        REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`] THEN
        REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN ABBREV_TAC `l = log(&1 + u) / M` THEN
  SUBGOAL_THEN `l * M = log(&1 + u)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN UNDISCH_TAC `~(M = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `indep_rv_family p s (\i x. (X:K->A->real) i x - expectation p (X i))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`;
                  `\t. t - expectation p ((X:K->A->real) i)`]
             MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
                 REAL_CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`;
                `\i x. (X:K->A->real) i x - expectation p (X i)`; `s:K->bool`;
                `l:real`; `\i. M - expectation p ((X:K->A->real) i)`]
           EXPECTATION_EXP_SUM_INDEP) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:K->A->real) i x <= M}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN ABBREV_TAC `c = (exp(l * M) - &1 - l * M) / M pow 2` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--(l * e)) * exp(V * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `exp(--(l * e)) *
       expectation p (\x. exp(l *
                              sum s (\i.
                                         (X:K->A->real) i x -
                                         expectation p (X i))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL[`p:A prob_space`;
                    `\x. sum s (\i. (X:K->A->real) i x - expectation p (X i))`;
                    `l:real`; `e:real`] CHERNOFF_EXPECTATION_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL[`p:A prob_space`;
                    `\i x. (X:K->A->real) i x - expectation p (X i)`;
                    `s:K->bool`] RANDOM_VARIABLE_SUM_FINITE) THEN
      ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST; ETA_AX];
      ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `M:real`; `l:real`]
             BENNETT_MGF_CENTRED) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC EXPECTATION_POS THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "c" THEN
  REWRITE_TAC[ASSUME `l * M = log(&1 + u)`] THEN
  SIMP_TAC[EXP_LOG; ASSUME `&0 < &1 + u`] THEN
  UNDISCH_TAC `l * M = log(&1 + u)` THEN
  UNDISCH_TAC `(M:real) * e / V = u` THEN UNDISCH_TAC `~(M = &0)` THEN
  UNDISCH_TAC `~(V = &0)` THEN ABBREV_TAC `L = log(&1 + u)` THEN
  CONV_TAC REAL_FIELD);;

let MGF_CENTRED_QUADRATIC_BOUND = prove
 (`!p:A prob_space X M l c.
        random_variable p X /\ integrable p (\x. X x pow 2) /\
        almost_surely p {x | X x <= M} /\ &0 <= l /\
        (!x. x <= M ==> exp(l * x) <= &1 + l * x + c * x pow 2)
        ==> integrable p (\x. exp(l * (X x - expectation p X))) /\
            expectation p (\x. exp(l * (X x - expectation p X))) <=
            exp(expectation p (\x. X x pow 2) * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (X:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN ABBREV_TAC `m = expectation p (X:A->real)` THEN
  SUBGOAL_THEN `integrable p (\x. exp(l * (X:A->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `exp(l * M)` THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_EXP_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:A->real) x <= M}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ABS_EXP; REAL_EXP_MONO_LE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. exp(l * ((X:A->real) x - m))) = (\x. exp(--(l * m)) * exp(l * X x))`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM REAL_EXP_ADD] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(l * m)) *
     exp(l * m + expectation p (\x. (X:A->real) x pow 2) * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `expectation p (\x. &1 + l * (X:A->real) x + c * X x pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
      ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CONST; INTEGRABLE_CMUL] THEN
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | (X:A->real) x <= M}` THEN ASM_SIMP_TAC[IN_ELIM_THM];
      ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_ADD; INTEGRABLE_CONST;
                   INTEGRABLE_CMUL; EXPECTATION_CMUL; EXPECTATION_CONST] THEN
      MP_TAC(SPEC `l * m + expectation p (\x. (X:A->real) x pow 2) * c`
               REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC]);;

let EXP_SUM_CENTRED_TAIL = prove
 (`!p:A prob_space (X:K->A->real) s M l c e.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> integrable p (\x. X i x pow 2) /\
                    almost_surely p {x | X i x <= M}) /\
    &0 <= l /\ (!x. x <= M ==> exp(l * x) <= &1 + l * x + c * x pow 2)
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x - expectation p (X i)) >= e} <=
        exp(--(l * e) + sum s (\i. expectation p (\x. X i x pow 2)) * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> expectation p ((X:K->A->real) i) <= M`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\x:A. M:real`]
             EXPECTATION_MONO_AE) THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `indep_rv_family p s (\i x. (X:K->A->real) i x - expectation p (X i))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INDEP_RV_FAMILY_COMPOSE THEN EXISTS_TAC `X:K->A->real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`;
                  `\t. t - expectation p ((X:K->A->real) i)`]
             MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID;
                 REAL_CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`;
                `\i x. (X:K->A->real) i x - expectation p (X i)`; `s:K->bool`;
                `l:real`; `\i. M - expectation p ((X:K->A->real) i)`]
           EXPECTATION_EXP_SUM_INDEP) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:K->A->real) i x <= M}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN REWRITE_TAC[REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(--(l * e)) *
     expectation p (\x. exp(l *
                            sum s (\i. (X:K->A->real) i x -
                                       expectation p (X i))))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`;
                  `\x. sum s (\i. (X:K->A->real) i x - expectation p (X i))`;
                  `l:real`; `e:real`] CHERNOFF_EXPECTATION_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`;
                  `\i x. (X:K->A->real) i x - expectation p (X i)`;
                  `s:K->bool`] RANDOM_VARIABLE_SUM_FINITE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST; ETA_AX];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN ASM_SIMP_TAC[REAL_EXP_SUM] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `M:real`; `l:real`;
                `c:real`] MGF_CENTRED_QUADRATIC_BOUND) THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC EXPECTATION_POS THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

let BENNETT_NULL_EVENT = prove
 (`!p:A prob_space (X:K->A->real) s M e.
    FINITE s /\
    (!i. i IN s ==> random_variable p (X i) /\
                    integrable p (\x. X i x pow 2) /\
                    almost_surely p {x | X i x <= M}) /\
    &0 <= e /\ &0 < sum s (\i. expectation p (\x. X i x pow 2)) /\
    M * e / sum s (\i. expectation p (\x. X i x pow 2)) <= -- &1
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x - expectation p (X i)) >= e} = &0`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
    `V = sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2))` THEN
  ABBREV_TAC `u = (M:real) * e / V` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> expectation p ((X:K->A->real) i) <= M`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`; `\x:A. M:real`]
             EXPECTATION_MONO_AE) THEN
    ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; ETA_AX];
    ALL_TAC] THEN MATCH_MP_TAC PROB_ZERO_OUTSIDE_ALMOST_SURELY THEN
  EXISTS_TAC `{x | !i. i IN s ==> x IN {y | (X:K->A->real) i y <= M}}` THEN
  ASM_SIMP_TAC[ALMOST_SURELY_FINITE_FORALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MP_TAC(ISPECL[`p:A prob_space`;
                  `\i x. (X:K->A->real) i x - expectation p (X i)`;
                  `s:K->bool`] RANDOM_VARIABLE_SUM_FINITE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST; ETA_AX];
    ALL_TAC] THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN X_GEN_TAC `x:A` THEN
  STRIP_TAC THEN REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  ASM_CASES_TAC `!i. i IN s ==> (X:K->A->real) i x <= M` THENL
   [ALL_TAC;
    ASM_MESON_TAC[]] THEN SUBGOAL_THEN `M < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= u` MP_TAC THENL
     [EXPAND_TAC "u" THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `e <= sum s (\i. (X:K->A->real) i x - expectation p (X i))` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[TAUT `~a ==> b <=> ~b ==> a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(s:K->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
      `sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2)) = V` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum s (\i. M - expectation p ((X:K->A->real) i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[REAL_ARITH `(a:real) <= b ==> a - c <= b - c`];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC
    `sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2) / --M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LT_ALL THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `M < &0 ==> &0 < --M`] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
             EXPECTATION_POW2_GE) THEN ASM_SIMP_TAC[] THEN
    ABBREV_TAC `m = expectation p ((X:K->A->real) i)` THEN
    MP_TAC(SPEC `M:real` REAL_LT_POW_2) THEN
    ASM_SIMP_TAC[REAL_ARITH `M < &0 ==> ~(M = &0)`] THEN
    MP_TAC(SPEC `m - M / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `M < &0 ==> &0 < --M`] THEN
    UNDISCH_TAC `u <= -- &1` THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let BERNSTEIN_LOG_AUX = prove
 (`!u. -- &1 < u
       ==> (&0 <= u
            ==> &3 * u * (&6 + u) / (&2 * (&3 + u) pow 2) <= log(&1 + u)) /\
           (u <= &0
            ==> log(&1 + u) <= &3 * u * (&6 + u) / (&2 * (&3 + u) pow 2))`,
  SUBGOAL_THEN
    `!a b. -- &1 < a /\ a <= b
           ==> log(&1 + a) - &3 * a * (&6 + a) / (&2 * (&3 + a) pow 2)
               <= log(&1 + b) - &3 * b * (&6 + b) / (&2 * (&3 + b) pow 2)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL[`\y. log(&1 + y) -
                       &3 * y * (&6 + y) / (&2 * (&3 + y) pow 2)`;
                  `\y. inv(&1 + y) - &27 / (&3 + y) pow 3`; `{y | -- &1 < y}`;
                  `a:real`; `b:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
      REPEAT CONJ_TAC THEN
      TRY(REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC) THEN
      SUBGOAL_THEN `~(&1 + y = &0) /\ ~(&3 + y = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &1 + y /\ &0 < &3 + y` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= y pow 2 * (&9 + y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL[`&0`; `u:real`]);
    FIRST_X_ASSUM(MP_TAC o SPECL[`u:real`; `&0`])] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let BERNSTEIN_THETA_GE = prove
 (`!u. -- &1 < u
       ==> u pow 2 / (&2 * (&1 + u / &3)) <= (&1 + u) * log(&1 + u) - u`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `u pow 2 / (&2 * (&1 + u / &3)) = &3 * u pow 2 / (&2 * (&3 + u))`
    SUBST1_TAC THENL
   [UNDISCH_TAC `-- &1 < u` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a - b ==> b <= a`) THEN
  SUBGOAL_THEN
    `!y. -- &1 < y
         ==> ((\y. ((&1 + y) * log(&1 + y) - y) -
                   &3 * y pow 2 / (&2 * (&3 + y)))
              has_real_derivative
                (log(&1 + y) - &3 * y * (&6 + y) / (&2 * (&3 + y) pow 2)))
             (atreal y)`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    SUBGOAL_THEN `~(&1 + y = &0) /\ ~(&3 + y = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC
    `f =
     \y. ((&1 + y) * log(&1 + y) - y) - &3 * y pow 2 / (&2 * (&3 + y))` THEN
  SUBGOAL_THEN `(f:real->real)(&0) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[REAL_ADD_RID; LOG_1] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN SUBGOAL_THEN `&0 <= (f:real->real) u` MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= u \/ u <= &0`) THEN
  SUBGOAL_THEN `(f:real->real)(&0) <= f u` MP_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_INCREASING_IMP THEN
    EXISTS_TAC
      `\y. log(&1 + y) - &3 * y * (&6 + y) / (&2 * (&3 + y) pow 2)` THEN
    EXISTS_TAC `{y | &0 <= y}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MP_TAC(SPEC `y:real` BERNSTEIN_LOG_AUX) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_DECREASING_IMP THEN
    EXISTS_TAC
      `\y. log(&1 + y) - &3 * y * (&6 + y) / (&2 * (&3 + y) pow 2)` THEN
    EXISTS_TAC `{y | -- &1 < y /\ y <= &0}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN
    TRY ASM_REAL_ARITH_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `y:real` BERNSTEIN_LOG_AUX) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]]);;

let SHEET_FORM_PREP = prove
 (`!p:A prob_space (X:K->A->real) s M.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> expectation p (X i) = &0 /\
                    almost_surely p {x | abs(X i x) <= M})
    ==> (!i. i IN s ==> integrable p (\x. X i x pow 2) /\
                        almost_surely p {x | X i x <= M}) /\
        (!x. sum s (\i. X i x - expectation p (X i)) = sum s (\i. X i x)) /\
        &(CARD s) * sum s (\i. variance p (X i)) / &(CARD s) =
        sum s (\i. expectation p (\x. X i x pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p (\x. (X:K->A->real) i x pow 2)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `(M:real) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:K->A->real) i x) <= M}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ABS_POW] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:K->A->real) i x) <= M}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[REAL_SUB_RZERO];
    ASM_CASES_TAC `CARD(s:K->bool) = 0` THENL
     [SUBGOAL_THEN `s:K->bool = {}` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[CARD_EQ_0];
        REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `i:K` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`] VARIANCE_ALT) THEN
      ASM_SIMP_TAC[INTEGRABLE_POW2_IMP] THEN REAL_ARITH_TAC]]);;

let BERNSTEIN_INEQUALITY_GEN = prove
 (`!p:A prob_space (X:K->A->real) s M e.
    FINITE s /\
    indep_rv_family p s X /\
    (!i. i IN s ==> integrable p (\x. X i x pow 2) /\
                    almost_surely p {x | X i x <= M}) /\ &0 <= e
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x - expectation p (X i)) >= e} <=
        exp(--(e pow 2) /
            (&2 * (sum s (\i. expectation p (\x. X i x pow 2)) +
                   M * e / &3)))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
    `V = sum s (\i. expectation p (\x. (X:K->A->real) i x pow 2))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I[indep_rv_family]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> integrable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_POW2_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i IN s ==> &0 <= expectation p (\x. (X:K->A->real) i x pow 2)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EXPECTATION_POS THEN
    ASM_SIMP_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `{x | x IN prob_carrier p /\
      sum s (\i. (X:K->A->real) i x - expectation p (X i)) >= e} IN
     prob_events p`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MP_TAC(ISPECL[`p:A prob_space`;
                  `\i x. (X:K->A->real) i x - expectation p (X i)`;
                  `s:K->bool`] RANDOM_VARIABLE_SUM_FINITE) THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_SUB; RANDOM_VARIABLE_CONST; ETA_AX];
    ALL_TAC] THEN ASM_CASES_TAC `V = &0` THENL
   [ASM_CASES_TAC `e = &0` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
      ASM_SIMP_TAC[PROB_LE_1] THEN
      ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_NEG_0; real_div;
                      REAL_MUL_LZERO; REAL_EXP_0; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= y`) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN
    SUBGOAL_THEN
      `!i. i IN s ==> almost_surely p {x | (X:K->A->real) i x pow 2 = &0}`
      ASSUME_TAC THENL
     [MP_TAC(ISPECL[`\i. expectation p (\x. (X:K->A->real) i x pow 2)`;
                    `s:K->bool`] SUM_POS_EQ_0) THEN ASM_SIMP_TAC[] THEN
      DISCH_TAC THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      MATCH_MP_TAC EXPECTATION_AS_NONNEG_ZERO THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `prob_carrier (p:A prob_space)` THEN
      REWRITE_TAC[ALMOST_SURELY_CARRIER; IN_ELIM_THM; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `!i. i IN s ==> expectation p ((X:K->A->real) i) = &0`
      ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL[`p:A prob_space`; `\x:A. &0`; `(X:K->A->real) i`]
               EXPECTATION_AS_EQ) THEN
      ASM_SIMP_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN ANTS_TAC THENL
       [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
        EXISTS_TAC `{x | (X:K->A->real) i x pow 2 = &0}` THEN
        ASM_SIMP_TAC[IN_ELIM_THM; REAL_POW_EQ_0; ARITH_EQ] THEN MESON_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN MATCH_MP_TAC PROB_ZERO_OUTSIDE_ALMOST_SURELY THEN
    EXISTS_TAC
      `{x | !i. i IN s ==> x IN {y | (X:K->A->real) i y pow 2 = &0}}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_FINITE_FORALL] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_POW_EQ_0; ARITH_EQ] THEN X_GEN_TAC `x:A` THEN
    STRIP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC
      `sum s (\i. (X:K->A->real) i x - expectation p (X i)) >= e` THEN
    SUBGOAL_THEN `sum s (\i. (X:K->A->real) i x - expectation p (X i)) = &0`
      SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[REAL_SUB_REFL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN SUBGOAL_THEN `&0 < V` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_CASES_TAC `M = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `&0`;
                  `(e:real) / V`; `((e:real) / V) pow 2 / &2`; `e:real`]
             EXP_SUM_CENTRED_TAIL) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `(e:real) / V * y` EXP_LE_QUADRATIC_NONPOS) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a * y <= &0 <=> &0 <= a * --y`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `a = b ==> x <= exp a ==> x <= exp b`) THEN
    UNDISCH_TAC `&0 < V` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN ASM_CASES_TAC `(M:real) * e / V <= -- &1` THENL
   [MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= y`) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN MATCH_MP_TAC BENNETT_NULL_EVENT THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `M:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `M:real`;
                `e:real`] BENNETT_INEQUALITY_GEN) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `(M:real) * e / V` BERNSTEIN_THETA_GE) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `--(V / M pow 2) *
     (((M:real) * e / V) pow 2 / (&2 * (&1 + (M * e / V) / &3)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `&0 < &1 + (M * e / V) / &3 /\ &0 < V + M * e / &3` MP_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `V + M * e / &3 = V * (&1 + (M * e / V) / &3)`
      SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < V` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN UNDISCH_TAC `~(M = &0)` THEN UNDISCH_TAC `&0 < V` THEN
  CONV_TAC REAL_FIELD);;

let BENNETT_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s M e sigma2.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> expectation p (X i) = &0 /\
                    almost_surely p {x | abs(X i x) <= M}) /\
    sigma2 = sum s (\i. variance p (X i)) / &(CARD s) /\ &0 <= e
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= e} <=
        exp(--(&(CARD s) * sigma2 / M pow 2) *
            ((&1 + M * e / (&(CARD s) * sigma2)) *
             log(&1 + M * e / (&(CARD s) * sigma2)) -
             M * e / (&(CARD s) * sigma2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `M:real`]
           SHEET_FORM_PREP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `M:real`;
                `e:real`] BENNETT_INEQUALITY_GEN) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_div; REAL_MUL_ASSOC]) THEN
  ASM_REWRITE_TAC[]);;

let BERNSTEIN_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s M e sigma2.
    FINITE s /\ indep_rv_family p s X /\
    (!i. i IN s ==> expectation p (X i) = &0 /\
                    almost_surely p {x | abs(X i x) < M}) /\
    sigma2 = sum s (\i. variance p (X i)) / &(CARD s) /\ &0 <= e
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= e} <=
        exp(--(e pow 2) / (&2 * (&(CARD s) * sigma2 + M * e / &3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `M:real`]
           SHEET_FORM_PREP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:K->A->real) i x) < M}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `M:real`;
                `e:real`] BERNSTEIN_INEQUALITY_GEN) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_div; REAL_MUL_ASSOC]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chernoff 1: Pr[X >= t] <= E[a^X] / a^t for a >= 1, and the series form    *)
(* for natural-number-valued X.                                              *)
(* ------------------------------------------------------------------------- *)

let CHERNOFF_PGF_INEQUALITY_GEN = prove
 (`!p:A prob_space X a t.
    random_variable p X /\ &1 <= a /\ integrable p (\x. a rpow X x)
    ==> prob p {x | x IN prob_carrier p /\ X x >= t} <=
        expectation p (\x. a rpow X x) / a rpow t`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. a rpow y = exp(log a * y)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[rpow] THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`; `log a`; `t:real`]
           CHERNOFF_EXPECTATION_BOUND) THEN ASM_SIMP_TAC[LOG_POS] THEN
  REWRITE_TAC[real_div; REAL_EXP_NEG; GSYM REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let CHERNOFF_PGF_INEQUALITY = prove
 (`!p:A prob_space X a t.
    random_variable p X /\ almost_surely p {x | ?k. X x = &k} /\ &1 <= a /\
    real_summable (from 0)
      (\k. prob p {x | x IN prob_carrier p /\ X x = &k} * a pow k)
    ==> prob p {x | x IN prob_carrier p /\ X x >= t} <=
        real_infsum (from 0)
          (\k. prob p {x | x IN prob_carrier p /\ X x = &k} * a pow k) /
        a rpow t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a rpow t` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `A = \k. {x | x IN prob_carrier p /\ (X:A->real) x = &k /\ X x >= t}` THEN
  SUBGOAL_THEN `!k. (A:num->A->bool) k IN prob_events p` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x | x IN prob_carrier p /\ (X:A->real) x = &k /\ X x >= t} =
                  {x | x IN prob_carrier p /\ X x = &k} INTER
                  {x | x IN prob_carrier p /\ X x >= t}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PROB_INTER_IN_EVENTS THEN
    ASM_SIMP_TAC[RANDOM_VARIABLE_LEVEL_SET; RV_PREIMAGE_GE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `A:num->A->bool`]
    PROB_COUNTABLY_ADDITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    DISCH_TAC THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                                    NOT_IN_EMPTY] THEN
    GEN_TAC THEN ASM_CASES_TAC `(X:A->real) x = &i` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `prob p (UNIONS {(A:num->A->bool) n | n IN (:num)})` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `almost_surely p {x | ?k. (X:A->real) x = &k}` THEN
    REWRITE_TAC[almost_surely; null_event] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `UNIONS {(A:num->A->bool) n | n IN (:num)} IN prob_events p`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PROB_COUNTABLE_UNION_IN_EVENTS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `prob p (UNIONS {(A:num->A->bool) n | n IN (:num)} UNION N0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PROB_MONO THEN
      ASM_SIMP_TAC[PROB_UNION_IN_EVENTS; RV_PREIMAGE_GE] THEN
      EXPAND_TAC "A" THEN
      REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_CASES_TAC `?k. (X:A->real) x = &k` THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]];
      MP_TAC(ISPECL [`p:A prob_space`;
                     `UNIONS {(A:num->A->bool) n | n IN (:num)}`;
                     `N0:A->bool`] PROB_SUBADDITIVE) THEN
      ASM_REWRITE_TAC[REAL_ADD_RID]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_LE THEN
  MAP_EVERY EXISTS_TAC
   [`\k. prob p ((A:num->A->bool) k)`;
    `\k. inv(a rpow t) *
         (prob p {x | x IN prob_carrier p /\ (X:A->real) x = &k} * a pow k)`;
    `from 0`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\k. prob p {x | x IN prob_carrier p /\ (X:A->real) x = &k} * a pow k`;
      `real_infsum (from 0)
         (\k. prob p {x | x IN prob_carrier p /\ (X:A->real) x = &k} *
              a pow k)`;
      `inv(a rpow t)`; `from 0`] REAL_SERIES_LMUL) THEN
    ASM_REWRITE_TAC[REAL_SUMS_INFSUM] THEN REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= prob p {x | x IN prob_carrier p /\ (X:A->real) x = &k}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PROB_POSITIVE THEN ASM_SIMP_TAC[RANDOM_VARIABLE_LEVEL_SET];
    ALL_TAC] THEN
  ASM_CASES_TAC `&k >= t` THENL
   [SUBGOAL_THEN `(A:num->A->bool) k = {x | x IN prob_carrier p /\ X x = &k}`
    SUBST1_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM RPOW_POW] THEN MATCH_MP_TAC RPOW_MONO_LE THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(A:num->A->bool) k = {}` SUBST1_TAC THENL
     [EXPAND_TAC "A" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[PROB_EMPTY; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sums of k-wise independent variables in [0,1] (Schmidt, Siegel and        *)
(* Srinivasan): the generalized binomial coefficient                         *)
(*   C(t,k) = prod_{j=1..k} (t - j + 1) / k!,                                *)
(* the bound C(sum x_i, k) <= e_k(x), and, for k < t + 1,                    *)
(*   Pr[sum X_i >= t] <= C(n,k) (mu/n)^k / C(t,k).                           *)
(* ------------------------------------------------------------------------- *)

let SYMMETRIC_MEAN_LE_POW = prove
 (`!s:K->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i)
     ==> symmetric_mean s a k <= symmetric_mean s a 1 pow k`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SYMMETRIC_MEAN_0; real_pow; REAL_LE_REFL];
    ALL_TAC] THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[GSYM ONE; REAL_POW_1; REAL_LE_REFL];
    ALL_TAC] THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `k:num` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_POS_LE];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `symmetric_mean (s:K->bool) a k pow (k + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[ADD1] THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_POW_MONO];
    ALL_TAC] THEN REWRITE_TAC[REAL_POW_POW; ADD1] THEN
  SUBGOAL_THEN `(k + 1) * k = k * (k + 1)` SUBST1_TAC THENL
   [ARITH_TAC;
    ALL_TAC] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_POS_LE]);;

let GBINOM_SUC = prove
 (`!y k. product(1..SUC k) (\j. y - &j + &1) / &(FACT(SUC k)) =
         (product(1..k) (\j. y - &j + &1) / &(FACT k)) * (y - &k) / &(SUC k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`; FACT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN `&0 < &(FACT k)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT];
    ALL_TAC] THEN CONV_TAC REAL_FIELD);;

let GBINOM_0 = prove
 (`!y. product(1..0) (\j. y - &j + &1) / &(FACT 0) = &1`,
  REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; FACT] THEN REAL_ARITH_TAC);;

let GBINOM_POS_LE = prove
 (`!y k. &k <= y + &1 ==> &0 <= product(1..k) (\j. y - &j + &1) / &(FACT k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `j <= k:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_REAL_ARITH_TAC);;

let GBINOM_POS_LT = prove
 (`!y k. &k < y + &1 ==> &0 < product(1..k) (\j. y - &j + &1) / &(FACT k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
  REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
  MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN UNDISCH_TAC `j <= k:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC);;

let GBINOM_MONO = prove
 (`!y z k. &k <= y + &1 /\ y <= z
           ==> product(1..k) (\j. y - &j + &1) / &(FACT k) <=
               product(1..k) (\j. z - &j + &1) / &(FACT k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN UNDISCH_TAC `j <= k:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC);;

let GBINOM_STEP = prove
 (`!k y c. &k - &1 <= y /\ &0 <= c /\ c <= &1 /\ &k <= y + c
     ==> product(1..SUC k) (\j. (y + c) - &j + &1) / &(FACT(SUC k)) <=
         (if &k <= y then product(1..SUC k) (\j. y - &j + &1) / &(FACT(SUC k))
          else &0) +
         c * product(1..k) (\j. y - &j + &1) / &(FACT k)`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GBINOM_SUC; GBINOM_0] THEN
    REWRITE_TAC[GSYM ONE; REAL_DIV_1; REAL_MUL_LID; REAL_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL[`y:real`; `c:real`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN REWRITE_TAC[GBINOM_SUC; GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN `&k <= y` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = product(1..k) (\j. y - &j + &1) / &(FACT k)` THEN
  ABBREV_TAC `B = product(1..k) (\j. (y + c) - &j + &1) / &(FACT k)` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC GBINOM_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(A * (y - &k) / (&k + &1) + c * A) *
     ((y + c) - (&k + &1)) / ((&k + &1) + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN
      `((A * (y - &k) / (&k + &1)) * (y - (&k + &1)) / ((&k + &1) + &1) +
        c * A * (y - &k) / (&k + &1)) -
       (A * (y - &k) / (&k + &1) + c * A) *
       ((y + c) - (&k + &1)) / ((&k + &1) + &1) =
       A * (c * (&k + &1) * (&1 - c)) / ((&k + &1) * ((&k + &1) + &1))`
      SUBST1_TAC THENL
     [MP_TAC(SPEC `k:num` REAL_POS) THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC];
    SUBGOAL_THEN
      `(&0 + c * A * (y - &k) / (&k + &1)) -
       (A * (y - &k) / (&k + &1) + c * A) *
       ((y + c) - (&k + &1)) / ((&k + &1) + &1) =
       A *
       (c * (&k + &1) * (&1 - c) - (y - &k - &1) * (y - &k)) /
       ((&k + &1) * ((&k + &1) + &1))`
      SUBST1_TAC THENL
     [MP_TAC(SPEC `k:num` REAL_POS) THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ b <= &0 ==> &0 <= a - b`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ONCE_REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= --a * b`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC]]);;

let GBINOM_1 = prove
 (`!y. product(1..1) (\j. y - &j + &1) / &(FACT 1) = y`,
  GEN_TAC THEN MP_TAC(SPECL[`y:real`; `0`] GBINOM_SUC) THEN
  REWRITE_TAC[GBINOM_0; GSYM ONE; REAL_MUL_LID; REAL_SUB_RZERO; REAL_DIV_1]);;

let GBINOM_LE_SUM_PRODUCT_SUBSETS = prove
 (`!s:K->bool x.
     FINITE s /\ (!i. i IN s ==> &0 <= x i /\ x i <= &1)
     ==> !k. &k <= sum s x + &1
             ==> product(1..k) (\j. sum s x - &j + &1) / &(FACT k) <=
                 sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t x)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`s:K->bool`, `s:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `k = 0 \/ k = 1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `&k <= &0 + &1` THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_OF_NUM_LE] THEN ARITH_TAC;
      ASM_REWRITE_TAC[GBINOM_0; SUM_PRODUCT_SUBSETS_0; REAL_LE_REFL];
      ASM_REWRITE_TAC[SUM_PRODUCT_SUBSETS_1; SUM_CLAUSES; GBINOM_1;
                      REAL_LE_REFL]];
    ALL_TAC] THEN MAP_EVERY X_GEN_TAC[`a:K`; `s:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(fun ih -> STRIP_TAC THEN
    MP_TAC(MATCH_MP ih
      (ASSUME `!i. i IN s ==> &0 <= (x:K->real) i /\ x i <= &1`))) THEN
  DISCH_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
  SUBST1_TAC(REAL_ARITH `(x:K->real) a + sum s x = sum s x + x a`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[GBINOM_0; SUM_PRODUCT_SUBSETS_0; REAL_LE_REFL];
    ALL_TAC] THEN DISCH_TAC THEN ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_INSERT] THEN
  MP_TAC(SPECL[`k:num`; `sum s (x:K->real)`; `(x:K->real) a`] GBINOM_STEP) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a:real) <= a' /\ b <= b' ==> x <= a + b ==> x <= a' + b'`) THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check(is_forall o concl)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC[FINITE_RESTRICTED_POWERSET] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_MESON_TAC[SUBSET; HAS_SIZE]];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check(is_forall o concl)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_SUC]) THEN
    ASM_REAL_ARITH_TAC]);;

let SUM_PRODUCT_SUBSETS_LE_MEAN_POW = prove
 (`!s:K->bool a k.
     FINITE s /\ (!i. i IN s ==> &0 <= a i)
     ==> sum {t | t SUBSET s /\ t HAS_SIZE k} (\t. product t a) <=
         &(binom(CARD s,k)) * (sum s a / &(CARD s)) pow k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_PRODUCT_SUBSETS_SYMMETRIC_MEAN] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  SUBGOAL_THEN `symmetric_mean (s:K->bool) a 1 = sum s a / &(CARD s)`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[symmetric_mean; SUM_PRODUCT_SUBSETS_1; BINOM_1];
    ALL_TAC] THEN ASM_SIMP_TAC[SYMMETRIC_MEAN_LE_POW]);;

let CHERNOFF_KWISE_CORE = prove
 (`!p:A prob_space (X:K->A->real) s k t.
    FINITE s /\
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    &k < t + &1
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= t} <=
        &(binom(CARD s,k)) *
        (sum s (\i. expectation p (X i)) / &(CARD s)) pow k /
        (product(1..k) (\j. t - &j + &1) / &(FACT k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE
                  I[kwise_indep_rv_family]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Cb = product(1..k) (\j. t - &j + &1) / &(FACT k)` THEN
  SUBGOAL_THEN `&0 < Cb` ASSUME_TAC THENL
   [EXPAND_TAC "Cb" THEN MATCH_MP_TAC GBINOM_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `TS = {u | u SUBSET (s:K->bool) /\ u HAS_SIZE k}` THEN
  SUBGOAL_THEN `FINITE (TS:(K->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "TS" THEN ASM_REWRITE_TAC[FINITE_RESTRICTED_POWERSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!u. u IN TS
         ==> integrable p (\x. product u (\i. (X:K->A->real) i x)) /\
             expectation p (\x. product u (\i. X i x)) =
             product u (\i. expectation p (X i))`
    ASSUME_TAC THENL
   [EXPAND_TAC "TS" THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_EXPECTATION_PRODUCT THEN
    MAP_EVERY EXISTS_TAC[`X:K->A->real`; `k:num`; `s:K->bool`] THEN
    ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM CDF_GENERATED_SING] THEN
      MATCH_MP_TAC MEASURABLE_WRT_CDF_GENERATED THEN REWRITE_TAC[IN_SING];
      EXISTS_TAC `&1` THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | &0 <= (X:K->A->real) i x /\ X i x <= &1}` THEN
      CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC
    `E = {x | x IN prob_carrier p /\ sum s (\i. (X:K->A->real) i x) >= t}` THEN
  SUBGOAL_THEN `(E:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `expectation p (\x. sum TS (\u. product u (\i. (X:K->A->real) i x)))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `prob p E * Cb = expectation p (\x:A. Cb * indicator_fn E x)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[EXPECTATION_CMUL; INTEGRABLE_INDICATOR; ETA_AX;
                   EXPECTATION_INDICATOR] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN MATCH_MP_TAC EXPECTATION_MONO_AE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_INDICATOR; ETA_AX] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM_FINITE THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
      `{x | !i. i IN s ==> x IN
          {y | &0 <= (X:K->A->real) i y /\ X i y <= &1}}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_FINITE_FORALL] THEN
    REWRITE_TAC[IN_ELIM_THM; indicator_fn] THEN X_GEN_TAC `x:A` THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC SUM_POS_LE THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "TS" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_MESON_TAC[SUBSET; HAS_SIZE]] THEN
    SUBGOAL_THEN `t <= sum s (\i. (X:K->A->real) i x)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN E` THEN EXPAND_TAC "E" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN REWRITE_TAC[REAL_MUL_RID] THEN EXPAND_TAC "Cb" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `product(1..k) (\j. sum s (\i. (X:K->A->real) i x) - &j + &1) /
       &(FACT k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GBINOM_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL[`s:K->bool`; `\i. (X:K->A->real) i x`]
             GBINOM_LE_SUM_PRODUCT_SUBSETS) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN EXPAND_TAC "TS" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `TS:(K->bool)->bool`;
                `\u x. product u (\i. (X:K->A->real) i x)`]
           EXPECTATION_SUM_FINITE) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum TS (\u. product u (\i. expectation p ((X:K->A->real) i)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN EXPAND_TAC "TS" THEN
  MP_TAC(ISPECL[`s:K->bool`; `\i. expectation p ((X:K->A->real) i)`; `k:num`]
           SUM_PRODUCT_SUBSETS_LE_MEAN_POW) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `(X:K->A->real) i`]
           EXPECTATION_UNIT_BOUNDS) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chernoff 6 and 7: the k-wise bound for 0/1 variables with a common mean,  *)
(* and with k-hat = ceiling(mu d / (1 - mu / n)) <= k.                       *)
(* ------------------------------------------------------------------------- *)

let CHERNOFF_KWISE_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s k q t.
    FINITE s /\
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | X i x = &0 \/ X i x = &1} /\
                    expectation p (X i) = q) /\
    &k < t + &1
    ==> prob p {x | x IN prob_carrier p /\ sum s (\i. X i x) >= t} <=
        &(binom(CARD s,k)) * q pow k /
        (product(1..k) (\j. t - &j + &1) / &(FACT k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `k:num`;
                `t:real`] CHERNOFF_KWISE_CORE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (X:K->A->real) i x = &0 \/ X i x = &1}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) = c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `sum s (\i. expectation p ((X:K->A->real) i)) = &(CARD s) * q`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_CONST] THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `CARD(s:K->bool) = 0` THENL
   [ASM_REWRITE_TAC[] THEN STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
    REWRITE_TAC[binom; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO];
    ASM_SIMP_TAC[REAL_OF_NUM_EQ;
                 REAL_FIELD `~(n = &0) ==> (n * q) / n = q`]]);;

let CHERNOFF_KWISE_UNIT_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s k mu d kh.
    FINITE s /\
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    mu = sum s (\i. expectation p (X i)) /\
    &kh = --floor(--(mu * d / (&1 - mu / &(CARD s)))) /\ kh <= k
    ==> prob p {x | x IN prob_carrier p /\
                    sum s (\i. X i x) >= (&1 + d) * mu} <=
        &(binom(CARD s,kh)) * (mu / &(CARD s)) pow kh /
        (product(1..kh) (\j. (&1 + d) * mu - &j + &1) / &(FACT kh))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> random_variable p ((X:K->A->real) i)`
    ASSUME_TAC THENL [ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT]; ALL_TAC] THEN
  ABBREV_TAC
    `E =
     {x | x IN prob_carrier p /\
      sum s (\i. (X:K->A->real) i x) >= (&1 + d) * mu}` THEN
  SUBGOAL_THEN `(E:A->bool) IN prob_events p` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN ASM_CASES_TAC `kh = 0` THENL
   [ASM_REWRITE_TAC[binom; real_pow; PRODUCT_CLAUSES_NUMSEG; FACT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[PROB_LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mu /\ mu <= &(CARD(s:K->bool))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[EXPECTATION_UNIT_BOUNDS];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum s (\i:K. &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[EXPECTATION_UNIT_BOUNDS];
        ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_LE_REFL]]];
    ALL_TAC] THEN ABBREV_TAC `y = mu * d / (&1 - mu / &(CARD(s:K->bool)))` THEN
  SUBGOAL_THEN `&kh - &1 < y /\ y <= &kh` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `--(y:real)` FLOOR) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `&1 <= &kh` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `~(CARD(s:K->bool) = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&0 < y` THEN EXPAND_TAC "y" THEN
    SUBGOAL_THEN `mu = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `mu <= &(CARD(s:K->bool))` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - mu / &(CARD(s:K->bool))` ASSUME_TAC THENL
   [SUBGOAL_THEN `mu / &(CARD(s:K->bool)) <= &1` MP_TAC THENL
     [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
               ASSUME `~(CARD(s:K->bool) = 0)`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN UNDISCH_TAC `&0 < y` THEN EXPAND_TAC "y" THEN
    REWRITE_TAC[ASSUME `mu / &(CARD(s:K->bool)) = &1`] THEN
    REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_INV_0; REAL_MUL_RZERO;
                REAL_LT_REFL];
    ALL_TAC] THEN ASM_CASES_TAC `(&1 + d) * mu <= &(CARD(s:K->bool))` THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `kh:num`;
                  `(&1 + d) * mu`] CHERNOFF_KWISE_CORE) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_MONO THEN EXISTS_TAC `k:num` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN SUBGOAL_THEN `y <= (&1 + d) * mu` MP_TAC THENL
       [EXPAND_TAC "y" THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ;
                 ASSUME `&0 < &1 - mu / &(CARD(s:K->bool))`] THEN
        SUBGOAL_THEN `((&1 + d) * mu) * (mu / &(CARD(s:K->bool))) <= mu`
          MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&(CARD(s:K->bool)) * (mu / &(CARD(s:K->bool)))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN
            REWRITE_TAC[ASSUME `(&1 + d) * mu <= &(CARD(s:K->bool))`] THEN
            MATCH_MP_TAC REAL_LE_DIV THEN
            REWRITE_TAC[REAL_POS; ASSUME `&0 <= mu`];
            SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ;
                     ASSUME `~(CARD(s:K->bool) = 0)`; REAL_LE_REFL]];
          REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME
                      `mu =
                       sum s (\i. expectation p ((X:K->A->real) i))`)] THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
    MATCH_MP_TAC PROB_ZERO_OUTSIDE_ALMOST_SURELY THEN
    EXISTS_TAC
      `{x | !i. i IN s ==> x IN
          {x | &0 <= (X:K->A->real) i x /\ X i x <= &1}}` THEN
    REWRITE_TAC[ASSUME `(E:A->bool) IN prob_events p`] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL[`p:A prob_space`;
                    `\i. {x | &0 <= (X:K->A->real) i x /\ X i x <= &1}`;
                    `s:K->bool`] ALMOST_SURELY_FINITE_FORALL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `sum s (\i. (X:K->A->real) i x) <= sum s (\i:K. &1)`
      MP_TAC THENL [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[SUM_CONST; ASSUME `FINITE(s:K->bool)`; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_CASES_TAC `CARD(s:K->bool) < kh` THENL
   [ASM_SIMP_TAC[BINOM_LT; REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS; ASSUME `&0 <= mu`];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
  MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&j <= &(CARD(s:K->bool))` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Central moments of sums of k-wise independent variables in [0,1]:        *)
(*   E[(sum X_i - mu)^k] <= C_k (nk/e)^(k/2),                                *)
(*   C_k = 2 sqrt(pi k) exp(1/(6k)),                                         *)
(* for even k >= 2, and the tail bound (kth moment 2) by Markov's inequality *)
(* on the k-th power.                                                        *)
(* ------------------------------------------------------------------------- *)

let KWISE_INDEP_RV_FAMILY_EXPECTATION_PRODUCT_POW = prove
 (`!p:A prob_space (X:K->A->real) k s u e B.
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | abs(X i x) <= B}) /\
    u SUBSET s /\ FINITE u /\ CARD u <= k
    ==> integrable p (\x. product u (\i. X i x pow e i)) /\
        expectation p (\x. product u (\i. X i x pow e i)) =
        product u (\i. expectation p (\x. X i x pow e i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `\i:K y:real. y pow e i`;
                `u:K->bool`]
           INDEP_RV_FAMILY_EXPECTATION_PRODUCT_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `k:num`; `u:K->bool`; `X:K->A->real`]
             KWISE_INDEP_RV_FAMILY_EQ_INDEP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_SUBSET THEN EXISTS_TAC `s:K->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    EXISTS_TAC `abs B pow e(i:K)` THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:K->A->real) i x) <= B}` THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC] THEN REWRITE_TAC[IN_ELIM_THM; REAL_ABS_POW] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]);;

let KWISE_INDEP_SUM_POW_PRODUCT_FACTOR = prove
 (`!p:A prob_space (X:K->A->real) k s B.
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | abs(X i x) <= B})
    ==> !t. FINITE t
            ==> !m u e. t SUBSET s /\ u SUBSET s /\ DISJOINT t u /\ FINITE u /\
                        m + CARD u <= k
                ==> integrable p
                      (\x. sum t (\i. X i x) pow m *
                           product u (\i. X i x pow e i)) /\
                    expectation p
                      (\x. sum t (\i. X i x) pow m *
                           product u (\i. X i x pow e i)) =
                    expectation p (\x. sum t (\i. X i x) pow m) *
                    product u (\i. expectation p (\x. X i x pow e i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p:A prob_space`; `X:K->A->real`; `k:num`; `s:K->bool`;
                   `u:K->bool`; `e:K->num`; `B:real`]
      KWISE_INDEP_RV_FAMILY_EXPECTATION_PRODUCT_POW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES] THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; EXPECTATION_CONST] THEN
    ASM_REWRITE_TAC[REAL_POW_ZERO; REAL_MUL_LZERO; INTEGRABLE_CONST;
                    EXPECTATION_CONST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!m u e. b INSERT t SUBSET s /\ u SUBSET s /\ DISJOINT (b INSERT t) u /\
            FINITE u /\ m + CARD u <= k
     ==> !j. j <= m
             ==> integrable p
                   (\x. sum t (\i. (X:K->A->real) i x) pow (m - j) *
                        (X b x pow j * product u (\i. X i x pow e i))) /\
                 expectation p
                   (\x. sum t (\i. X i x) pow (m - j) *
                        (X b x pow j * product u (\i. X i x pow e i))) =
                 expectation p (\x. sum t (\i. X i x) pow (m - j)) *
                 expectation p (\x. X b x pow j) *
                 product u (\i. expectation p (\x. X i x pow e i))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((b:K) IN u)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `j = 0` THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; SUB_0; EXPECTATION_CONST] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `u:K->bool`; `e:K->num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`m - j:num`; `(b:K) INSERT u`;
       `\i:K. if i = b then j else (e:K->num) i`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT] THEN
      REPEAT CONJ_TAC THEN FIRST [ASM_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
    SUBGOAL_THEN
     `(!x. product u (\i. (X:K->A->real) i x pow (if i = b then j else e i)) =
           product u (\i. X i x pow e i)) /\
      product u
        (\i. expectation p
               (\x. (X:K->A->real) i x pow (if i = b then j else e i))) =
      product u (\i. expectation p (\x. X i x pow e i))`
    (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((i:K) = b)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m u e. b INSERT t SUBSET s /\ u SUBSET s /\ DISJOINT (b INSERT t) u /\
            FINITE u /\ m + CARD u <= k
     ==> integrable p (\x. sum (b INSERT t) (\i. (X:K->A->real) i x) pow m *
                           product u (\i. X i x pow e i)) /\
         expectation p (\x. sum (b INSERT t) (\i. X i x) pow m *
                            product u (\i. X i x pow e i)) =
         sum (0..m) (\j. &(binom(m,j)) *
                         (expectation p (\x. sum t (\i. X i x) pow (m - j)) *
                          expectation p (\x. X b x pow j) *
                          product u (\i. expectation p (\x. X i x pow e i))))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `u:K->bool`; `e:K->num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `!x. sum (b INSERT t) (\i. (X:K->A->real) i x) pow m *
          product u (\i. X i x pow e i) =
          sum (0..m) (\j. &(binom(m,j)) *
                          (sum t (\i. X i x) pow (m - j) *
                           (X b x pow j * product u (\i. X i x pow e i))))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
      REWRITE_TAC[REAL_BINOMIAL_THEOREM; GSYM SUM_RMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!j. j IN 0..m
          ==> integrable p (\x. &(binom(m,j)) *
                  (sum t (\i. (X:K->A->real) i x) pow (m - j) *
                   (X b x pow j * product u (\i. X i x pow e i)))) /\
              expectation p (\x. &(binom(m,j)) *
                  (sum t (\i. X i x) pow (m - j) *
                   (X b x pow j * product u (\i. X i x pow e i)))) =
              &(binom(m,j)) *
              (expectation p (\x. sum t (\i. X i x) pow (m - j)) *
               expectation p (\x. X b x pow j) *
               product u (\i. expectation p (\x. X i x pow e i)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUM_FINITE; EXPECTATION_SUM_FINITE;
                 FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `{}:K->bool`; `e:K->num`]) THEN
  REWRITE_TAC[PRODUCT_CLAUSES; REAL_MUL_RID; EMPTY_SUBSET; DISJOINT_EMPTY;
              FINITE_EMPTY; CARD_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `u:K->bool`; `e:K->num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let BINOMIAL_MOMENT_STEP_BOUND = prove
 (`!m x E (a:num->real) w.
    &0 < x /\ &0 <= E /\
    (!j. j <= m ==> abs(a j) <= &(FACT j) * E / x pow j) /\
    w 0 = &1 /\ w 1 = &0 /\ (!j. 2 <= j ==> abs(w j) <= &1 / &4)
    ==> abs(sum(0..m) (\j. &(binom(m,j)) * a(m - j) * w j)) <=
        &(FACT m) * E * exp((exp x - &1 - x) / &4) / x pow m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `sum(0..m) (\j. (&(FACT m) * E / x pow m) *
                    (x pow j / &(FACT j) * abs((w:num->real) j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
      `&(binom(m,j)) * (&(FACT(m - j)) * E / x pow (m - j)) *
       abs((w:num->real) j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check(free_in `a:num->real` o concl)) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&(FACT m) = &(FACT(m - j)) * &(FACT j) * &(binom(m,j))`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL] THEN AP_TERM_TAC THEN
      MP_TAC(SPECL[`m - j:num`; `j:num`] BINOM_FACT) THEN
      ASM_SIMP_TAC[SUB_ADD];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `&0 < x pow j /\ &0 < x pow (m - j) /\ &0 < &(FACT j) /\
       x pow m = x pow (m - j) * x pow j`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; FACT_LT; GSYM REAL_POW_ADD;
                   SUB_ADD];
      ALL_TAC] THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < x pow j` THEN
    UNDISCH_TAC `&0 < &(FACT j)` THEN UNDISCH_TAC `&0 < x pow (m - j)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `&0 <= &(FACT m) * E / x pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&(FACT m) * E / x pow m) * exp((exp x - &1 - x) / &4)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + (exp x - &1 - x) / &4` THEN
  REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[SUM_SING_NUMSEG; real_pow; FACT; REAL_DIV_1; REAL_MUL_LID;
                    REAL_ABS_NUM] THEN MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:num->real. sum(0..m) f = f 0 + f 1 + sum(2..m) f`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL[`f:num->real`; `0`; `m:num`] SUM_CLAUSES_LEFT) THEN
    MP_TAC(ISPECL[`f:num->real`; `1`; `m:num`] SUM_CLAUSES_LEFT) THEN
    ASM_SIMP_TAC[LE_0; ARITH_RULE `~(m = 0) ==> 1 <= m`] THEN
    REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN MP_TAC(SPECL[`m:num`; `x:real`] REAL_EXP_PARTIAL_SUM_LE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_REWRITE_TAC[real_pow; FACT; ARITH; REAL_ABS_NUM; REAL_POW_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
                 `b <= a * inv(&4)
                  ==> &1 / &1 + x / &1 + a <= exp x
                  ==> &1 / &1 * &1 + x / &1 * &0 + b
                      <= &1 + (exp x - &1 - x) / &4`) THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check(free_in `w:num->real` o
        concl)) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let KWISE_INDEP_SUM_POW_INSERT = prove
 (`!p:A prob_space (X:K->A->real) k s B t b m.
    kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | abs(X i x) <= B}) /\
    FINITE t /\ ~(b IN t) /\ b INSERT t SUBSET s /\ m <= k
    ==> integrable p (\x. sum (b INSERT t) (\i. X i x) pow m) /\
        expectation p (\x. sum (b INSERT t) (\i. X i x) pow m) =
        sum (0..m) (\j. &(binom(m,j)) *
                        expectation p (\x. sum t (\i. X i x) pow (m - j)) *
                        expectation p (\x. X b x pow j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `k:num`; `s:K->bool`;
                `B:real`] KWISE_INDEP_SUM_POW_PRODUCT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:K->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `!j. j IN 0..m
         ==> integrable p
               (\x. &(binom(m,j)) *
                    (X b x pow j *
                     sum t (\i. (X:K->A->real) i x) pow (m - j))) /\
             expectation p (\x. &(binom(m,j)) *
                                (X b x pow j * sum t (\i. X i x) pow (m - j)))
             =
             &(binom(m,j)) *
             expectation p (\x. sum t (\i. X i x) pow (m - j)) *
             expectation p (\x. X b x pow j)`
    ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `j = 0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL[`m:num`; `{}:K->bool`; `\i:K. 0`]) THEN
      ASM_REWRITE_TAC[real_pow; SUB_0; EXPECTATION_CONST; PRODUCT_CLAUSES;
                      EMPTY_SUBSET; DISJOINT_EMPTY; FINITE_EMPTY; CARD_CLAUSES;
                      ADD_CLAUSES; REAL_MUL_RID; REAL_MUL_LID] THEN
      ANTS_TAC THENL
       [ASM SET_TAC[];
        ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL[`m - j:num`; `{b:K}`; `\i:K. j:num`]) THEN
    REWRITE_TAC[PRODUCT_SING; FINITE_SING; CARD_SING] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST[ASM_ARITH_TAC; ASM SET_TAC[]];
      STRIP_TAC] THEN
    SUBGOAL_THEN
      `!x. (X:K->A->real) b x pow j * sum t (\i. X i x) pow (m - j) =
           sum t (\i. X i x) pow (m - j) * X b x pow j`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN ASM_SIMP_TAC[INTEGRABLE_CMUL; EXPECTATION_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. sum (b INSERT t) (\i. (X:K->A->real) i x) pow m =
         sum (0..m)
           (\j. &(binom(m,j)) * (X b x pow j * sum t (\i. X i x) pow (m - j)))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_SIMP_TAC[SUM_CLAUSES; REAL_BINOMIAL_THEOREM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRABLE_SUM_FINITE; EXPECTATION_SUM_FINITE;
               FINITE_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0]);;

let KWISE_SUM_MOMENT_EXP_BOUND = prove
 (`!p:A prob_space (X:K->A->real) k s x.
    FINITE s /\ kwise_indep_rv_family p k s X /\
    (!i. i IN s
         ==> almost_surely p {y | abs(X i y) <= &1} /\
             expectation p (X i) = &0 /\
             (!j. 2 <= j
                  ==> abs(expectation p (\y. X i y pow j)) <= &1 / &4)) /\
    &0 < x
    ==> !m. m <= k
            ==> abs(expectation p (\y. sum s (\i. X i y) pow m)) <=
                &(FACT m) * exp(&(CARD s) * (exp x - &1 - x) / &4) / x pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!t. FINITE t
         ==> t SUBSET s
         ==> !m. m <= k ==> abs(expectation p
                                  (\y. sum t (\i. (X:K->A->real) i y) pow m))
             <= &(FACT m) * exp(&(CARD t) * (exp x - &1 - x) / &4) / x pow m`
    (fun th -> ASM_SIMP_TAC[th; SUBSET_REFL]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES; REAL_MUL_LZERO; REAL_EXP_0;
                REAL_MUL_RID] THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[real_pow; EXPECTATION_CONST; FACT; REAL_POW_ZERO;
                    REAL_ABS_NUM; REAL_DIV_1; REAL_LE_REFL] THEN
    TRY(CONV_TAC REAL_RAT_REDUCE_CONV) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN MAP_EVERY X_GEN_TAC[`b:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `k:num`; `s:K->bool`; `&1`;
                `t:K->bool`; `b:K`; `m:num`] KWISE_INDEP_SUM_POW_INSERT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
               REAL_MUL_LID; REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MP_TAC(SPECL[`m:num`; `x:real`;
               `exp(&(CARD(t:K->bool)) * (exp x - &1 - x) / &4)`;
               `\j. expectation p (\y. sum t (\i. (X:K->A->real) i y) pow j)`;
               `\j. expectation p (\y. (X:K->A->real) b y pow j)`]
           BINOMIAL_MOMENT_STEP_BOUND) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE; real_pow; EXPECTATION_CONST; REAL_POW_1;
                    ETA_AX] THEN
    SUBGOAL_THEN `(t:K->bool) SUBSET s /\ (b:K) IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[];
      ALL_TAC] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) = c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let EXP_1_LE_25_9 = prove
 (`exp(&1) <= &25 / &9`,
  MP_TAC E_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let EXP_1_LE_PI = prove
 (`exp(&1) <= pi`,
  MP_TAC E_APPROX_32 THEN MP_TAC PI_APPROX_32 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let EXP_1_MUL_LE_EXP = prove
 (`!z. exp(&1) * z <= exp z`,
  GEN_TAC THEN MP_TAC(SPEC `z - &1` REAL_EXP_LE_X) THEN
  REWRITE_TAC[REAL_EXP_SUB] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_EXP_POS_LT] THEN REAL_ARITH_TAC);;

let EXP_QUAD_RATIO_5_3 = prove
 (`(exp(&5 / &3) - &1 - &5 / &3) / (&5 / &3) pow 2 <= &3 / &2`,
  SUBGOAL_THEN `exp(&5 / &3) <= &41 / &6` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `3` THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_EXP_N] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 pow 5` THEN CONJ_TAC THENL
     [ALL_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    SUBGOAL_THEN `&5 = &5 * &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_EXP_POS_LE; EXP_1_BOUNDS];
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let KWISE_MOMENT_CONSTANT_AUX = prove
 (`!r. 1 <= r
       ==> exp(&1) * &(2 * r) * exp(&3 / &4 * &r) / exp(&1) pow r <=
           &2 * sqrt(pi * &(2 * r)) * exp(&1 / (&6 * &(2 * r)))`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `&1 <= &r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_RID; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `exp(&3 / &4 * &r) / exp(&r) = exp(--(&r / &4))`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_SUB] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * sqrt(pi * &2 * &r)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 * sqrt(pi * &2 * &r) = sqrt(&8 * pi * &r)`
      SUBST1_TAC THENL
     [SUBGOAL_THEN `&8 * pi * &r = &2 pow 2 * (pi * &2 * &r)` SUBST1_TAC THENL
       [REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_LE_MUL; PI_POS_LE; REAL_POS] THEN
      SIMP_TAC[POW_2_SQRT; REAL_POS];
      ALL_TAC] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_EXP_N] THEN
    SUBGOAL_THEN `&2 * --(&r / &4) = --(&r / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC;
      ALL_TAC] THEN REWRITE_TAC[REAL_EXP_NEG] THEN
    MP_TAC(SPEC `&r / &2` EXP_1_MUL_LE_EXP) THEN MP_TAC EXP_1_LE_PI THEN
    MP_TAC(SPEC `&r / &2` REAL_EXP_POS_LT) THEN
    MP_TAC(SPEC `&1` REAL_EXP_POS_LT) THEN REWRITE_TAC[REAL_EXP_N] THEN
    SPEC_TAC(`exp(&r / &2)`, `g:real`) THEN SPEC_TAC(`exp(&1)`, `e:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
      `e pow 2 * (&2 pow 2 * &r pow 2) * inv g = (&4 * e pow 2 * &r pow 2) / g`
      SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&8 * pi * &r) * (e * &r / &2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `(&8 * pi * &r) * (e * &r / &2) = (&4 * e * &r * &r) * pi`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * (e * e) * &r * &r = (&4 * e * &r * &r) * e`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; PI_POS_LE]];
    ALL_TAC] THEN GEN_REWRITE_TAC LAND_CONV[GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; PI_POS_LE];
    GEN_REWRITE_TAC LAND_CONV[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS]]);;

let KWISE_MOMENT_NUMERIC_BOUND = prove
 (`!k r n. k = 2 * r /\ 1 <= r /\ &0 < n /\ &k <= exp(&1) * n
    ==> &(FACT k) *
        exp(n * (exp(sqrt(&k / n)) - &1 - sqrt(&k / n)) / &4) /
        sqrt(&k / n) pow k
        <= &2 * sqrt(pi * &k) * exp(&1 / (&6 * &k)) *
           (n * &k / exp(&1)) pow r`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `x = sqrt(&k / n)` THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x /\ x pow 2 = &k / n /\ x <= &5 / &3`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN SUBGOAL_THEN `&0 < &k / n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV];
      ALL_TAC] THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < n`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&1) * n` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    MP_TAC EXP_1_LE_25_9 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp x - &1 - x <= &3 / &2 * (&k / n)` ASSUME_TAC THENL
   [MP_TAC(SPECL[`x:real`; `&5 / &3`] EXP_QUAD_RATIO_MONO) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN SUBGOAL_THEN `&0 < x pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN MP_TAC EXP_QUAD_RATIO_5_3 THEN REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP(REAL_ARITH
                                   `(b:real) <= c /\ a <= b ==> a <= c`)) THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < x pow 2`] THEN
    REWRITE_TAC[ASSUME `x pow 2 = &k / n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(n * (exp x - &1 - x) / &4) <= exp(&3 / &4 * &r)`
    ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `n * (&3 / &2 * (&k / n)) / &4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN UNDISCH_TAC `&0 < n` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN SUBGOAL_THEN `&0 < exp(&1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `x pow k = (&k / n) pow r /\
     (&k / exp(&1)) pow k = ((&k / n) * (n * &k / exp(&1)) / exp(&1)) pow r`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `x pow 2 = &k / n`); REAL_POW_POW] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `x pow 2 * (n * &k / exp(&1)) / exp(&1) = (&k / exp(&1)) pow 2`
      SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < n` THEN
      UNDISCH_TAC `&0 < exp(&1)` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(exp(&1) * &k * exp(&3 / &4 * &r) / exp(&1) pow r) *
     (n * &k / exp(&1)) pow r` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
      `&2 * sqrt(pi * &k) * exp(&1 / (&6 * &k)) * (n * &k / exp(&1)) pow r =
       (&2 * sqrt(pi * &k) * exp(&1 / (&6 * &k))) * (n * &k / exp(&1)) pow r`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `r:num` KWISE_MOMENT_CONSTANT_AUX) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS]]] THEN
  REWRITE_TAC[ASSUME `x pow k = (&k / n) pow r`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `(exp(&1) * &k * (&k / exp(&1)) pow k) *
     (exp(&3 / &4 * &r) / (&k / n) pow r)` THEN
  SUBGOAL_THEN `&0 < (&k / n) pow r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[FACT_LE_EXP_MUL_POW; REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REWRITE_TAC[ASSUME
                `(&k / exp(&1)) pow k =
                 ((&k / n) * (n * &k / exp(&1)) / exp(&1)) pow r`] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 < exp(&1) pow r /\ &0 < &k pow r /\ &0 < n pow r`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SPEC_TAC(`exp(&1) pow r`, `er:real`) THEN GEN_TAC THEN
  SPEC_TAC(`&k pow r`, `kr:real`) THEN GEN_TAC THEN
  SPEC_TAC(`(n:real) pow r`, `nr:real`) THEN GEN_TAC THEN
  SPEC_TAC(`exp(&3 / &4 * &r):real`, `c:real`) THEN GEN_TAC THEN
  CONV_TAC REAL_FIELD);;

let KWISE_INDEP_RV_FAMILY_SUB_CONST = prove
 (`!p:A prob_space k s (X:K->A->real) c.
    kwise_indep_rv_family p k s X
    ==> kwise_indep_rv_family p k s (\i x. X i x - c i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_COMPOSE THEN
  EXISTS_TAC `X:K->A->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(X:K->A->real) i`;
                 `\y. y - (c:K->real) i`]
    MEASURABLE_WRT_CDF_GENERATED_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST]]);;

let EXPECTATION_UNIT_CENTRED_MOMENTS = prove
 (`!p:A prob_space X.
    random_variable p X /\ almost_surely p {x | &0 <= X x /\ X x <= &1}
    ==> almost_surely p {x | abs(X x - expectation p X) <= &1} /\
        expectation p (\x. X x - expectation p X) = &0 /\
        (!j. 2 <= j
             ==> abs(expectation p (\x. (X x - expectation p X) pow j)) <=
                 &1 / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:A->real`] EXPECTATION_UNIT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = expectation p (X:A->real)` THEN
  SUBGOAL_THEN `almost_surely p {x | abs((X:A->real) x - c) <= &1}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN ASM_SIMP_TAC[EXPECTATION_SUB_CONST; REAL_SUB_REFL] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `random_variable p (\x. ((X:A->real) x - c) pow j)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p
       {x | abs(((X:A->real) x - c) pow j) <= (&1 - &2 * c) * X x + c pow 2}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (X:A->real) x /\ X x <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((X:A->real) y - c) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POW] THEN
      SUBGOAL_THEN `j = 2 + (j - 2)` SUBST1_TAC THENL
       [ASM_ARITH_TAC;
        ALL_TAC] THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW2_ABS] THEN
      GEN_REWRITE_TAC RAND_CONV[GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(X:A->real) y pow 2 <= X y` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN
        GEN_REWRITE_TAC RAND_CONV[GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `almost_surely p {x | abs(((X:A->real) x - c) pow j) <= &1}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((X:A->real) x - c) <= &1}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ABS_POW] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `integrable p (\x. ((X:A->real) x - c) pow j) /\
     integrable p (\x. abs(((X:A->real) x - c) pow j)) /\
     integrable p (\x. (&1 - &2 * c) * (X:A->real) x + c pow 2)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `&1` THEN
      ASM_SIMP_TAC[RANDOM_VARIABLE_ABS; REAL_ABS_ABS];
      MATCH_MP_TAC INTEGRABLE_ADD THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_CONST]];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x. abs(((X:A->real) x - c) pow j))` THEN
  ASM_SIMP_TAC[EXPECTATION_ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x. (&1 - &2 * c) * (X:A->real) x + c pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CMUL; INTEGRABLE_CONST;
               EXPECTATION_CMUL; EXPECTATION_CONST] THEN
  MP_TAC(SPEC `c - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let KWISE_CENTRED_MOMENT_BOUND = prove
 (`!p:A prob_space (X:K->A->real) s k.
    FINITE s /\ kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    EVEN k /\ 2 <= k
    ==> expectation p
          (\x. (sum s (\i. X i x) - sum s (\i. expectation p (X i))) pow k) <=
        &2 * sqrt(pi * &k) * exp(&1 / (&6 * &k)) *
        (&(CARD s) * &k / exp(&1)) pow (k DIV 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC o
                  REWRITE_RULE[EVEN_EXISTS]) THEN
  SUBGOAL_THEN `(2 * r) DIV 2 = r /\ 1 <= r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_MULT THEN ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Y = \i x. (X:K->A->real) i x - expectation p (X i)` THEN
  SUBGOAL_THEN
    `!x. sum s (\i. (X:K->A->real) i x) - sum s (\i. expectation p (X i)) =
         sum s (\i. (Y:K->A->real) i x)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Y" THEN ASM_SIMP_TAC[SUM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `kwise_indep_rv_family p (2 * r) s (Y:K->A->real)`
    ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN MATCH_MP_TAC KWISE_INDEP_RV_FAMILY_SUB_CONST THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i IN s
         ==> almost_surely p {y | abs((Y:K->A->real) i y) <= &1} /\
             expectation p (Y i) = &0 /\
             (!j. 2 <= j ==> abs(expectation p (\y. Y i y pow j)) <= &1 / &4)`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN EXPAND_TAC "Y" THEN
    MATCH_MP_TAC EXPECTATION_UNIT_CENTRED_MOMENTS THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p {x | abs(sum s (\i. (Y:K->A->real) i x)) <= &(CARD s)}`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `\i. {y | abs((Y:K->A->real) i y) <= &1}`;
                  `s:K->bool`] ALMOST_SURELY_FINITE_FORALL) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
                  REWRITE_TAC[th]) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\i:K. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&(2 * r) <= exp(&1) * &(CARD(s:K->bool))` THENL
   [SUBGOAL_THEN `&0 < &(CARD(s:K->bool))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN DISCH_TAC THEN
      UNDISCH_TAC `&(2 * r) <= exp(&1) * &(CARD(s:K->bool))` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NOT_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL[`p:A prob_space`; `Y:K->A->real`; `2 * r`; `s:K->bool`;
                  `sqrt(&(2 * r) / &(CARD(s:K->bool)))`]
             KWISE_SUM_MOMENT_EXP_BOUND) THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `2 * r`) THEN REWRITE_TAC[LE_REFL]] THEN
    MP_TAC(SPECL[`2 * r`; `r:num`; `&(CARD(s:K->bool))`]
             KWISE_MOMENT_NUMERIC_BOUND) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC REAL_LE_TRANS THEN
                  EXISTS_TAC(lhand(concl th)) THEN CONJ_TAC THENL
                   [ALL_TAC;
                    ACCEPT_TAC th]) THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN ABBREV_TAC `n = &(CARD(s:K->bool))` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `random_variable p (\x. sum s (\i. (Y:K->A->real) i x) pow (2 * r))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN
    ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `almost_surely p {x | sum s (\i. (Y:K->A->real) i x) pow (2 * r)
                      <= (n:real) pow (2 * r)} /\
     almost_surely p {x | abs(sum s (\i. (Y:K->A->real) i x) pow (2 * r))
                      <= (n:real) pow (2 * r)}`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs(sum s (\i. (Y:K->A->real) i x)) <= (n:real)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
    REWRITE_TAC[REAL_ABS_ABS; REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `expectation p (\x:A. (n:real) pow (2 * r))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
    MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `(n:real) pow (2 * r)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN REWRITE_TAC[EXPECTATION_CONST; GSYM REAL_POW_POW] THEN
  SUBGOAL_THEN `&0 < exp(&1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(n * &(2 * r) / exp(&1)) pow r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN GEN_REWRITE_TAC LAND_CONV[GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_POW_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]] THEN
  GEN_REWRITE_TAC LAND_CONV[REAL_ARITH `&1 = &1 * &1`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= y ==> &1 <= &2 * y`) THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_ONE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &1` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ALL_TAC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN CONJ_TAC THENL
     [MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      ASM_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS]]);;

let MARKOV_POW_RESCALE = prove
 (`!P E c a t r. P <= E / t pow (2 * r) /\ E <= c * a pow r /\ &0 < t
                 ==> P <= c * (a / t pow 2) pow r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (t:real) pow (2 * r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(E:real) / t pow (2 * r)` THEN
  ASM_REWRITE_TAC[REAL_POW_DIV; REAL_POW_POW] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ]);;

let KTH_MOMENT_KWISE_INEQUALITY = prove
 (`!p:A prob_space (X:K->A->real) s k t.
    FINITE s /\ kwise_indep_rv_family p k s X /\
    (!i. i IN s ==> almost_surely p {x | &0 <= X i x /\ X i x <= &1}) /\
    EVEN k /\ 2 <= k /\ &0 < t
    ==> prob p {x | x IN prob_carrier p /\
                    abs(sum s (\i. X i x) - sum s (\i. expectation p (X i)))
                    >= t} <=
        &2 * sqrt(pi * &k) * exp(&1 / (&6 * &k)) *
        (&(CARD s) * &k / (exp(&1) * t pow 2)) pow (k DIV 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i IN s
         ==> random_variable p ((X:K->A->real) i) /\ integrable p (X i) /\
             &0 <= expectation p (X i) /\ expectation p (X i) <= &1`
    ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `random_variable p ((X:K->A->real) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[KWISE_INDEP_RV_FAMILY_ALT];
      ALL_TAC] THEN ASM_SIMP_TAC[EXPECTATION_UNIT_BOUNDS];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `expectation p (\x. sum s (\i. (X:K->A->real) i x)) =
     sum s (\i. expectation p (X i))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL[`p:A prob_space`; `s:K->bool`; `X:K->A->real`]
             EXPECTATION_SUM_FINITE) THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\x. sum s (\i. (X:K->A->real) i x)`;
                `k:num`; `t:real`] KTH_MOMENT_INEQUALITY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUM_FINITE THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `&(CARD(s:K->bool)) pow k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_POW THEN
      MATCH_MP_TAC RANDOM_VARIABLE_SUB_CONST THEN
      MATCH_MP_TAC RANDOM_VARIABLE_SUM_FINITE THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`p:A prob_space`;
                  `\i. {x | &0 <= (X:K->A->real) i x /\ X i x <= &1}`;
                  `s:K->bool`] ALMOST_SURELY_FINITE_FORALL) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
                  REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_ABS_POW] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[GSYM SUM_SUB] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\i:K. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN
      DISCH_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:K`)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `X:K->A->real`; `s:K->bool`; `k:num`]
           KWISE_CENTRED_MOMENT_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC o
                  REWRITE_RULE[EVEN_EXISTS]) THEN
  SUBGOAL_THEN `(2 * r) DIV 2 = r`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC DIV_MULT THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `&(CARD(s:K->bool)) * &(2 * r) / (exp(&1) * t pow 2) =
     (&(CARD s) * &(2 * r) / exp(&1)) / t pow 2`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < exp(&1) /\ &0 < t pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_POW_LT];
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_ASSOC]) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC MARKOV_POW_RESCALE THEN
  EXISTS_TAC
    `expectation p (\x. (sum s (\i. (X:K->A->real) i x) -
                         sum s (\i. expectation p (X i))) pow
                        (2 * r))` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* For D with E[D | G] = 0 and |D| <= c almost surely, and Z >= 0 bounded    *)
(* and G-measurable: E[Z exp(l D)] <= exp(l^2 c^2 / 2) E[Z] (the integrated  *)
(* form of the conditional Hoeffding bound). Azuma's inequality for a        *)
(* martingale with |X_i - X_(i-1)| <= c_i almost surely:                     *)
(*   Pr[|X_n - X_0| >= d] <= 2 exp(-d^2 / (2 sum c_i^2)).                    *)
(* ------------------------------------------------------------------------- *)

let MARTINGALE_GEN_COND_EXP = prove
 (`!p:A prob_space FF X n.
    martingale p FF X
    ==> almost_surely p {x | gen_cond_exp p (FF n) (X (SUC n)) x = X n x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I[martingale]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filtration; adapted]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl)) THEN
  MATCH_MP_TAC GEN_COND_EXP_AE_UNIQUE THEN
  EXISTS_TAC `(FF:num->(A->bool)->bool) n` THEN
  ASM_SIMP_TAC[GEN_COND_EXP_MEASURABLE_WRT; GEN_COND_EXP_INTEGRABLE;
               GEN_COND_EXP_CONDITIONING; ETA_AX]);;

let GEN_COND_EXP_ZERO_ORTHOGONAL = prove
 (`!p:A prob_space G Z D K c.
    sub_sigma_algebra p G /\ measurable_wrt p G Z /\
    (!x. x IN prob_carrier p ==> abs(Z x) <= K) /\
    integrable p D /\ almost_surely p {x | gen_cond_exp p G D x = &0} /\
    almost_surely p {x | abs(D x) <= c}
    ==> integrable p (\x. Z x * D x) /\
        expectation p (\x. Z x * D x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integrable p (\x. (Z:A->real) x * D x)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `K * c:real` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_WRT_IMP_RV];
        ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE; ETA_AX]];
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | abs((D:A->real) x) <= c}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; REAL_ABS_MUL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`;
                 `\x. (Z:A->real) x * D x`] GEN_COND_EXP_TOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `\x:A. &0`;
                 `gen_cond_exp p G (\x. (Z:A->real) x * D x)`]
    EXPECTATION_AS_EQ) THEN
  REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_RANDOM_VARIABLE THEN
    MATCH_MP_TAC GEN_COND_EXP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `Z:A->real`;
                 `D:A->real`; `K:real`] GEN_COND_EXP_TAKE_OUT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  EXISTS_TAC `{x | gen_cond_exp p G (\w. (Z:A->real) w * D w) x =
                   Z x * gen_cond_exp p G D x} INTER
              {x | gen_cond_exp p G (D:A->real) x = &0}` THEN
  ASM_SIMP_TAC[ALMOST_SURELY_INTER] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let EXP_CHORD_SYMMETRIC = prove
 (`!l c d. &0 < c /\ abs d <= c
           ==> exp(l * d) <= (exp(l * c) + exp(--(l * c))) / &2 +
                             d / c * (exp(l * c) - exp(--(l * c))) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL[`l:real`; `--c:real`; `c:real`; `d:real`] CONVEX_BOUND_EXP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) = b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN UNDISCH_TAC `&0 < c` THEN
  CONV_TAC REAL_FIELD);;

let GEN_COND_EXP_ZERO_EXP_BOUND = prove
 (`!p:A prob_space G D Z K c l.
    sub_sigma_algebra p G /\ measurable_wrt p G Z /\
    almost_surely p {x | &0 <= Z x /\ Z x <= K} /\
    integrable p D /\ almost_surely p {x | gen_cond_exp p G D x = &0} /\
    almost_surely p {x | abs(D x) <= c}
    ==> integrable p (\x. Z x * exp(l * D x)) /\
        expectation p (\x. Z x * exp(l * D x)) <=
        exp(l pow 2 * c pow 2 / &2) * expectation p Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (Z:A->real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_WRT_IMP_RV]; ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (Z:A->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (Z:A->real) x /\ Z x <= K}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `random_variable p (D:A->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP ALMOST_SURELY_NONEMPTY o
      check (fun th -> can (find_term ((=) `c:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `integrable p (\x. (Z:A->real) x * exp(l * D x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_AS_BOUNDED THEN
    EXISTS_TAC `K * exp(abs l * c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RANDOM_VARIABLE_MUL THEN
      ASM_SIMP_TAC[RANDOM_VARIABLE_EXP_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (Z:A->real) x /\ Z x <= K} INTER
                {x | abs((D:A->real) x) <= c}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_INTER] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; REAL_ABS_MUL; REAL_ABS_EXP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(l * (D:A->real) x)` THEN
    REWRITE_TAC[REAL_ABS_LE; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= expectation p (Z:A->real)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:A prob_space`; `\x:A. &0`; `Z:A->real`]
      EXPECTATION_MONO_AE) THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; EXPECTATION_CONST; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | &0 <= (Z:A->real) x /\ Z x <= K}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[REAL_LE_LT] o
                check (fun th -> concl th = `&0 <= c`)) THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
                  check (fun th -> concl th = `&0 = c`)) THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; real_div;
                REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_LID] THEN
    MP_TAC(ISPECL [`p:A prob_space`; `Z:A->real`;
                   `\x. (Z:A->real) x * exp(l * D x)`] EXPECTATION_AS_EQ) THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE] THEN
    ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | abs((D:A->real) x) <= &0}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(D:A->real) x = &0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID]]] THEN
  ABBREV_TAC `W = \x. max (min ((Z:A->real) x) K) (&0)` THEN
  SUBGOAL_THEN `measurable_wrt p G (W:A->real) /\
                (!x. x IN prob_carrier p ==> abs(W x) <= abs K) /\
                almost_surely p {x | (W:A->real) x = Z x}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_MAX_CONST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURABLE_WRT_MIN_CONST THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | &0 <= (Z:A->real) x /\ Z x <= K}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:A prob_space`; `G:(A->bool)->bool`; `W:A->real`;
                 `D:A->real`; `abs K`; `c:real`]
    GEN_COND_EXP_ZERO_ORTHOGONAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integrable p (W:A->real) /\ expectation p W = expectation p (Z:A->real)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXPECTATION_AS_EQ THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_WRT_IMP_RV]; ALL_TAC] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (W:A->real) x = Z x}` THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `A = (exp(l * c) + exp(--(l * c))) / &2` THEN
  ABBREV_TAC `B = (exp(l * c) - exp(--(l * c))) / &2` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `expectation p (\x. A * (W:A->real) x + B / c * (W x * D x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EXPECTATION_MONO_AE THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC `{x | (W:A->real) x = Z x} INTER
                {x | &0 <= (Z:A->real) x /\ Z x <= K} INTER
                {x | abs((D:A->real) x) <= c}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_INTER] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`l:real`; `c:real`; `(D:A->real) x`]
      EXP_CHORD_SYMMETRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Z:A->real) x * (A + (D:A->real) x / c * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXPECTATION_ADD; INTEGRABLE_CMUL; EXPECTATION_CMUL] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "A" THEN
  MP_TAC(SPEC `l * c:real` REAL_COSH_LE_EXP_SQUARE) THEN
  REWRITE_TAC[REAL_EXP_NEG; REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let MARTINGALE_INCREMENT_GEN_COND_EXP = prove
 (`!p:A prob_space FF X n.
    martingale p FF X
    ==> almost_surely p
          {x | gen_cond_exp p (FF n) (\w. X (SUC n) w - X n w) x = &0}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [martingale]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filtration; adapted]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                 `(X:num->A->real) (SUC n)`; `(X:num->A->real) n`]
    GEN_COND_EXP_SUB) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `FF:num->(A->bool)->bool`;
                 `X:num->A->real`; `n:num`] MARTINGALE_GEN_COND_EXP) THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) n`;
                 `(X:num->A->real) n`] GEN_COND_EXP_SELF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun a -> DISCH_THEN(fun b -> DISCH_THEN(fun c ->
    MP_TAC(MATCH_MP ALMOST_SURELY_INTER
      (CONJ a (MATCH_MP ALMOST_SURELY_INTER (CONJ b c))))))) THEN
  DISCH_TAC THEN MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MARTINGALE_EXP_INCREMENT_BOUND = prove
 (`!p:A prob_space FF X m Z K c l.
    martingale p FF X /\ measurable_wrt p (FF m) Z /\
    almost_surely p {x | &0 <= Z x /\ Z x <= K} /\
    almost_surely p {x | abs(X (SUC m) x - X m x) <= c}
    ==> integrable p (\x. Z x * exp(l * (X (SUC m) x - X m x))) /\
        expectation p (\x. Z x * exp(l * (X (SUC m) x - X m x))) <=
        exp(l pow 2 * c pow 2 / &2) * expectation p Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A prob_space`; `(FF:num->(A->bool)->bool) m`;
                 `\x. (X:num->A->real) (SUC m) x - X m x`; `Z:A->real`;
                 `K:real`; `c:real`; `l:real`]
    GEN_COND_EXP_ZERO_EXP_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MARTINGALE_INCREMENT_GEN_COND_EXP] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [martingale]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filtration]) THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; ETA_AX]);;

let MARTINGALE_EXP_MGF_BOUND = prove
 (`!p:A prob_space FF X n c l.
    martingale p FF X /\
    (!i. 1 <= i /\ i <= n
         ==> almost_surely p {x | abs(X i x - X (i - 1) x) <= c i})
    ==> !m. m <= n
            ==> almost_surely p
                  {x | abs(X m x - X 0 x) <= sum(1..m) (\i. abs(c i))} /\
                integrable p (\x. exp(l * (X m x - X 0 x))) /\
                expectation p (\x. exp(l * (X m x - X 0 x))) <=
                exp(l pow 2 * sum(1..m) (\i. c i pow 2) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I[martingale]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[filtration; adapted]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl)) THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_ABS_0;
                INTEGRABLE_CONST; EXPECTATION_CONST] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_MUL_RZERO; real_div;
                REAL_MUL_LZERO; REAL_EXP_0; REAL_LE_REFL] THEN
    MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN EXISTS_TAC `(:A)` THEN
    REWRITE_TAC[ALMOST_SURELY_UNIV; IN_ELIM_THM; REAL_LE_REFL];
    ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC;
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC m` o check(fun th ->
        can(find_term((=) `c:num->real`)) (concl th) &&
        is_forall(concl th))) THEN
  ASM_REWRITE_TAC[SUC_SUB1; ARITH_RULE `1 <= SUC m`] THEN DISCH_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
  ABBREV_TAC `B = sum(1..m) (\i. abs((c:num->real) i))` THEN
  ABBREV_TAC `S = sum(1..m) (\i. (c:num->real) i pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
    EXISTS_TAC
      `{x | abs((X:num->A->real) m x - X 0 x) <= B} INTER
       {x | abs((X:num->A->real) (SUC m) x - X m x) <= c (SUC m)}` THEN
    ASM_SIMP_TAC[ALMOST_SURELY_INTER] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `FF:num->(A->bool)->bool`; `X:num->A->real`;
                `m:num`; `\x. exp(l * ((X:num->A->real) m x - X 0 x))`;
                `exp(abs l * B)`; `(c:num->real) (SUC m)`; `l:real`]
           MARTINGALE_EXP_INCREMENT_BOUND) THEN REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_WRT_COMP_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_WRT_CMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MEASURABLE_WRT_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC MEASURABLE_WRT_MONO THEN
        EXISTS_TAC `(FF:num->(A->bool)->bool) 0` THEN ASM_SIMP_TAC[LE_0];
        MP_TAC(SPECL[`&1`; `(:real)`] REAL_CONTINUOUS_ON_EXP_LMUL) THEN
        REWRITE_TAC[REAL_MUL_LID; ETA_AX]];
      MATCH_MP_TAC ALMOST_SURELY_SUBSET THEN
      EXISTS_TAC `{x | abs((X:num->A->real) m x - X 0 x) <= B}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(l * ((X:num->A->real) m x - X 0 x))` THEN
      REWRITE_TAC[REAL_ABS_LE; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!x. exp(l * ((X:num->A->real) m x - X 0 x)) *
         exp(l * (X (SUC m) x - X m x)) =
         exp(l * (X (SUC m) x - X 0 x))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `exp(l pow 2 * c (SUC m) pow 2 / &2) *
     expectation p (\x. exp(l * ((X:num->A->real) m x - X 0 x)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(l pow 2 * c (SUC m) pow 2 / &2) * exp(l pow 2 * S / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC]);;

let AZUMA_INEQUALITY_UPPER = prove
 (`!p:A prob_space FF X c n d.
    martingale p FF X /\
    (!i. 1 <= i /\ i <= n
         ==> almost_surely p {x | abs(X i x - X (i - 1) x) <= c i}) /\ &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ X n x - X 0 x >= d} <=
        exp(--(d pow 2) / (&2 * sum(1..n) (\i. c i pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `FF:num->(A->bool)->bool`; `X:num->A->real`;
                `n:num`; `c:num->real`;
                `d / sum(1..n) (\i. (c:num->real) i pow 2)`]
           MARTINGALE_EXP_MGF_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `random_variable p (\x. (X:num->A->real) n x - X 0 x)`
    ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I[martingale]) THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE; ETA_AX];
    ALL_TAC] THEN ABBREV_TAC `S = sum(1..n) (\i. (c:num->real) i pow 2)` THEN
  SUBGOAL_THEN `&0 < S \/ &0 = S` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_LT] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0; REAL_EXP_0] THEN
    MATCH_MP_TAC PROB_LE_1 THEN MATCH_MP_TAC RV_PREIMAGE_GE THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\x. (X:num->A->real) n x - X 0 x`;
                `(d:real) / S`; `d:real`] CHERNOFF_EXPECTATION_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--((d:real) / S * d)) * exp((d / S) pow 2 * S / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < S` THEN
    CONV_TAC REAL_FIELD]);;

let AZUMA_INEQUALITY = prove
 (`!p:A prob_space FF X c n d.
    martingale p FF X /\
    (!i. 1 <= i /\ i <= n
         ==> almost_surely p {x | abs(X i x - X (i - 1) x) <= c i}) /\ &0 <= d
    ==> prob p {x | x IN prob_carrier p /\ abs(X n x - X 0 x) >= d} <=
        &2 * exp(--(d pow 2) / (&2 * sum(1..n) (\i. c i pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`p:A prob_space`; `\x. (X:num->A->real) n x - X 0 x`; `d:real`]
           PROB_ABS_GE_LE_ADD) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I[martingale]) THEN
    MATCH_MP_TAC RANDOM_VARIABLE_SUB THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_RANDOM_VARIABLE; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`p:A prob_space`; `FF:num->(A->bool)->bool`; `X:num->A->real`;
                `c:num->real`; `n:num`; `d:real`] AZUMA_INEQUALITY_UPPER) THEN
  MP_TAC(ISPECL[`p:A prob_space`; `FF:num->(A->bool)->bool`;
                `\n x. --((X:num->A->real) n x)`; `c:num->real`; `n:num`;
                `d:real`] AZUMA_INEQUALITY_UPPER) THEN
  ASM_SIMP_TAC[MARTINGALE_NEG] THEN
  REWRITE_TAC[REAL_ARITH `abs(--(a:real) - --b) = abs(a - b)`;
              REAL_ARITH `--((a:real) - b) = --a - --b`] THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[REAL_ARITH
              `!a b e q:real. a <= e /\ b <= e /\ q <= b + a
                              ==> q <= &2 * e`]);;
