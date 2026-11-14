(* ========================================================================= *)
(* Inequalities about finite set systems and prefix-free codes, from         *)
(* L. Kozma, "Useful Inequalities" (v0.44).                                  *)
(* ========================================================================= *)

needs "Library/binomial.ml";;
needs "Library/agm.ml";;

(* ------------------------------------------------------------------------- *)
(* A family of subsets of a INSERT t splits into the members avoiding a and  *)
(* the members containing a, the latter with a removed.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_FAMILY_SPLIT_INSERT = prove
 (`!a t (A:(A->bool)->bool).
     FINITE t /\ ~(a IN t) /\ (!x. x IN A ==> x SUBSET a INSERT t)
     ==> CARD A = CARD {x | x SUBSET t /\ x IN A} +
                  CARD {x | x SUBSET t /\ (a INSERT x) IN A}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(A:(A->bool)->bool) =
    {x | x SUBSET t /\ x IN A} UNION
    IMAGE (\x. a INSERT x) {x | x SUBSET t /\ (a INSERT x) IN A}`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
  THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A->bool` THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_CASES_TAC `(a:A) IN x` THENL
     [DISJ2_TAC THEN EXISTS_TAC `x DELETE (a:A)` THEN
      ASM_SIMP_TAC[INSERT_DELETE] THEN ASM SET_TAC[];
      DISJ1_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. FINITE {x:A->bool | x SUBSET t /\ P x}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:A->bool | x SUBSET t}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{x:A->bool | x SUBSET t /\ x IN A}`;
    `IMAGE (\x:A->bool. a INSERT x) {x | x SUBSET t /\ (a INSERT x) IN A}`]
   CARD_UNION) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY;
                SUBSET] THEN
    ASM_MESON_TAC[IN_INSERT];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A->bool`; `y:A->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `(a:A) INSERT x = a INSERT y` THEN
  REWRITE_TAC[EXTENSION; IN_INSERT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FKG inequality for set systems: two up-sets (or two down-sets) in the     *)
(* power set of a finite set s are positively correlated.                    *)
(* ------------------------------------------------------------------------- *)

let FKG_INEQUALITY = prove
 (`!s (A:(A->bool)->bool) B.
     FINITE s /\
     (!x. x IN A ==> x SUBSET s) /\ (!x. x IN B ==> x SUBSET s) /\
     (!x y. x IN A /\ x SUBSET y /\ y SUBSET s ==> y IN A) /\
     (!x y. x IN B /\ x SUBSET y /\ y SUBSET s ==> y IN B)
     ==> CARD A * CARD B <= 2 EXP (CARD s) * CARD(A INTER B)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_EMPTY; CARD_CLAUSES; EXP; MULT_CLAUSES] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!C:(A->bool)->bool. (!x. x IN C ==> x = {}) /\ ~(C = {}) ==> C = {{}}`
    ASSUME_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      REWRITE_TAC[IN_SING] THEN MESON_TAC[MEMBER_NOT_EMPTY];
      ALL_TAC] THEN
    ASM_CASES_TAC `A:(A->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; MULT_CLAUSES; LE_0] THEN
    ASM_CASES_TAC `B:(A->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; MULT_CLAUSES; LE_0] THEN
    SUBGOAL_THEN `A:(A->bool)->bool = {{}} /\ B:(A->bool)->bool = {{}}`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INTER_IDEMPOT; CARD_SING; MULT_CLAUSES; LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "ih" o REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM])
   STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `A:(A->bool)->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `B:(A->bool)->bool` THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  MP_TAC(ISPECL [`a:A`; `t:A->bool`] CARD_FAMILY_SPLIT_INSERT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `A INTER B:(A->bool)->bool` th) THEN
    MP_TAC(SPEC `B:(A->bool)->bool` th) THEN
    MP_TAC(SPEC `A:(A->bool)->bool` th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_INTER; SET_RULE
   `{x | P x /\ Q x /\ R x} = {x | P x /\ Q x} INTER {x | P x /\ R x}`] THEN
  MATCH_MP_TAC(prove
   (`!a0 a1 b0 b1 c0 c1 n.
       a0 <= a1 /\ b0 <= b1 /\ a0 * b0 <= n * c0 /\ a1 * b1 <= n * c1
       ==> (a0 + a1) * (b0 + b1) <= (2 * n) * (c0 + c1)`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`&a1 - &a0:real`; `&b1 - &b0:real`] REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN ASM_REAL_ARITH_TAC)) THEN
  SUBGOAL_THEN `!P. FINITE {x:A->bool | x SUBSET t /\ P x}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:A->bool | x SUBSET t}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SET_RULE `!x t. x SUBSET t ==> x SUBSET (a:A) INSERT t`) THEN
  MP_TAC(SET_RULE `!x y. x SUBSET y ==> (a:A) INSERT x SUBSET a INSERT y`) THEN
  MP_TAC(SET_RULE `!x. x SUBSET (a:A) INSERT x`) THEN
  REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

let FKG_INEQUALITY_ALT = prove
 (`!s (A:(A->bool)->bool) B.
     FINITE s /\
     (!x. x IN A ==> x SUBSET s) /\ (!x. x IN B ==> x SUBSET s) /\
     (!x y. x IN A /\ y SUBSET x ==> y IN A) /\
     (!x y. x IN B /\ y SUBSET x ==> y IN B)
     ==> CARD A * CARD B <= 2 EXP (CARD s) * CARD(A INTER B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `IMAGE (\x:A->bool. s DIFF x) A`;
                 `IMAGE (\x:A->bool. s DIFF x) B`] FKG_INEQUALITY) THEN
  SUBGOAL_THEN
   `!C:(A->bool)->bool. (!x. x IN C ==> x SUBSET s)
                        ==> FINITE C /\
                            CARD(IMAGE (\x. s DIFF x) C) = CARD C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN ASM SET_TAC[];
      MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
        ASM_SIMP_TAC[FINITE_POWERSET] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:A->bool. s DIFF x) A INTER IMAGE (\x. s DIFF x) B =
    IMAGE (\x. s DIFF x) (A INTER B)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `z:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `x:A->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `y:A->bool` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `x:A->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `x:A->bool = y` (fun th -> ASM_MESON_TAC[th]) THEN
      MAP_EVERY UNDISCH_TAC
       [`z:A->bool = s DIFF x`; `z:A->bool = s DIFF y`] THEN
      SUBGOAL_THEN `(x:A->bool) SUBSET s /\ y SUBSET s` MP_TAC THENL
       [ASM_MESON_TAC[]; SET_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL [SET_TAC[]; SET_TAC[]; ALL_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A->bool`; `y:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s DIFF y:A->bool` THEN
  (CONJ_TAC THENL
    [UNDISCH_TAC `(y:A->bool) SUBSET s` THEN SET_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w:A->bool` THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(w:A->bool) SUBSET s` MP_TAC THENL
      [ASM_MESON_TAC[];
       MAP_EVERY UNDISCH_TAC
        [`x:A->bool = s DIFF w`; `(x:A->bool) SUBSET y`] THEN
       SET_TAC[]]]));;

(* ------------------------------------------------------------------------- *)
(* Kraft's inequality. A set W of words over a finite alphabet s is          *)
(* prefix-free if no word of W is a proper prefix of another. The leaves of  *)
(* a binary tree, as paths from the root, are a prefix-free set of binary    *)
(* words, and the depth of a leaf is the length of its word. For an infinite *)
(* W the sum is 0 in HOL; the bound for an infinite prefix-free set is this  *)
(* theorem applied to its finite subsets, which are again prefix-free.       *)
(* ------------------------------------------------------------------------- *)

let KRAFT_INEQUALITY_BOUNDED = prove
 (`!n s (W:(A list)->bool).
     FINITE s /\ FINITE W /\
     (!w. w IN W ==> ALL (\x. x IN s) w /\ LENGTH w <= n) /\
     (!u v. u IN W /\ APPEND u v IN W ==> v = [])
     ==> sum W (\w. inv(&(CARD s) pow LENGTH w)) <= &1`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (ASM_CASES_TAC `([]:A list) IN W` THENL
    [SUBGOAL_THEN `W = {[]:A list}` SUBST1_TAC THENL
      [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
       ASM_MESON_TAC[APPEND];
       REWRITE_TAC[SUM_SING; LENGTH; real_pow; REAL_INV_1; REAL_LE_REFL]];
     ALL_TAC])
  THENL
   [SUBGOAL_THEN `W:(A list)->bool = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[LE; LENGTH_EQ_NIL];
      REWRITE_TAC[SUM_CLAUSES; REAL_POS]];
    ALL_TAC] THEN
  ASM_CASES_TAC `W:(A list)->bool = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:A list. w IN W ==> ?a t. w = CONS a t /\ a IN s`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A list` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `w:A list` list_CASES) THEN ASM_MESON_TAC[ALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(s:A->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sum (s:A->bool) (\a. inv(&(CARD s)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RINV; REAL_OF_NUM_EQ; REAL_LE_REFL]] THEN
  MP_TAC(ISPECL
   [`HD:A list->A`; `\w:A list. inv(&(CARD(s:A->bool)) pow LENGTH w)`;
    `W:(A list)->bool`; `s:A->bool`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[HD];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN W /\ HD x = a} = IMAGE (CONS (a:A)) {v | CONS a v IN W}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:A list` THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[HD] THEN
    UNDISCH_TAC `!w:A list. w IN W ==> ?a t. w = CONS a t /\ a IN s` THEN
    DISCH_THEN(MP_TAC o SPEC `x:A list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` (X_CHOOSE_THEN `t:A list`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t:A list` THEN
    UNDISCH_TAC `HD(x:A list) = a` THEN UNDISCH_TAC `(x:A list) IN W` THEN
    ASM_REWRITE_TAC[HD] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_IMAGE; CONS_11; o_DEF; LENGTH; real_pow; REAL_INV_MUL;
           SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (TL:A list->A list) W` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[TL];
    ASM_MESON_TAC[ALL; LENGTH; LE_SUC];
    ASM_MESON_TAC[APPEND]]);;

let KRAFT_INEQUALITY_GEN = prove
 (`!s (W:(A list)->bool).
     FINITE s /\
     (!w. w IN W ==> ALL (\x. x IN s) w) /\
     (!u v. u IN W /\ APPEND u v IN W ==> v = [])
     ==> sum W (\w. inv(&(CARD s) pow LENGTH w)) <= &1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(W:(A list)->bool)` THENL
   [MP_TAC(ISPEC `IMAGE LENGTH (W:(A list)->bool)` num_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MATCH_MP_TAC KRAFT_INEQUALITY_BOUNDED THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(s:A->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    UNDISCH_TAC `~FINITE(W:(A list)->bool)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{[]:A list}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN
    X_GEN_TAC `w:A list` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `w:A list` list_CASES) THEN
    ASM_MESON_TAC[ALL; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &1`) THEN
  MATCH_MP_TAC SUM_DEGENERATE THEN
  ASM_REWRITE_TAC[REAL_INV_EQ_0; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
                  SET_RULE `!s:B->bool. {x | x IN s} = s`]);;

let KRAFT_INEQUALITY = prove
 (`!W:(bool list)->bool.
     (!u v. u IN W /\ APPEND u v IN W ==> v = [])
     ==> sum W (\w. inv(&2 pow LENGTH w)) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:bool)`; `W:(bool list)->bool`] KRAFT_INEQUALITY_GEN) THEN
  ASM_REWRITE_TAC[FINITE_BOOL; CARD_BOOL; IN_UNIV; ALL_T]);;

(* ------------------------------------------------------------------------- *)
(* The LYM inequality for an antichain A of subsets of a finite set s.       *)
(* ------------------------------------------------------------------------- *)

let LYM_INEQUALITY = prove
 (`!s (A:(A->bool)->bool).
     FINITE s /\ (!x. x IN A ==> x SUBSET s) /\
     (!x y. x IN A /\ y IN A /\ x SUBSET y ==> x = y)
     ==> sum A (\x. inv(&(binom(CARD s,CARD x)))) <= &1`,
  SUBGOAL_THEN
   `!n s (A:(A->bool)->bool).
      FINITE s /\ CARD s = n /\ (!x. x IN A ==> x SUBSET s) /\
      (!x y. x IN A /\ y IN A /\ x SUBSET y ==> x = y)
      ==> sum A (\x. inv(&(binom(n,CARD x)))) <= &1`
   (fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[]) THEN
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  (ASM_CASES_TAC `(s:A->bool) IN A` THENL
    [SUBGOAL_THEN `A = {s:A->bool}` SUBST1_TAC THENL
      [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
       ASM_MESON_TAC[];
       FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[SUM_SING; BINOM_REFL; REAL_INV_1; REAL_LE_REFL]];
     ALL_TAC])
  THENL
   [SUBGOAL_THEN `s:A->bool = {}` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `A:(A->bool)->bool = {}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[SUBSET_EMPTY];
      REWRITE_TAC[SUM_CLAUSES; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(A:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A->bool.
      x IN A
      ==> inv(&(binom(SUC n,CARD x))) =
          inv(&(SUC n)) *
          sum {y | y IN s /\ ~(y IN x)} (\y. inv(&(binom(n,CARD x))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A->bool) SUBSET s /\ ~(x = s)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `CARD(x:A->bool) <= n` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LT_SUC_LE] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check
       (fun th -> concl th = `CARD(s:A->bool) = SUC n`)) THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `{y | y IN s /\ ~(y IN x)} = (s:A->bool) DIFF x`
    SUBST1_TAC THENL
     [SET_TAC[]; ASM_SIMP_TAC[SUM_CONST; FINITE_DIFF; CARD_DIFF]] THEN
    MP_TAC(SPECL [`n:num`; `CARD(x:A->bool)`] BINOM_TOP_STEP) THEN
    MP_TAC(SPECL [`n:num`; `CARD(x:A->bool)`] BINOM_EQ_0) THEN
    MP_TAC(SPECL [`n + 1`; `CARD(x:A->bool)`] BINOM_EQ_0) THEN
    ASM_REWRITE_TAC[ADD1; GSYM NOT_LE] THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= n ==> k <= n + 1`; GSYM REAL_OF_NUM_EQ;
                 GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB;
                 GSYM REAL_OF_NUM_ADD] THEN
    SPEC_TAC(`&(binom(n,CARD(x:A->bool))):real`,`b0:real`) THEN
    SPEC_TAC(`&(binom(n + 1,CARD(x:A->bool))):real`,`b1:real`) THEN
    SPEC_TAC(`&(CARD(x:A->bool)):real`,`k:real`) THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN SPEC_TAC(`&n:real`,`m:real`) THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum A (\x:A->bool. inv(&(SUC n)) *
                       sum {y | y IN s /\ ~(y IN x)}
                           (\y. inv(&(binom(n,CARD x)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\x:A->bool y:A. ~(y IN x)`; `\x:A->bool y:A. inv(&(binom(n,CARD x)))`;
    `A:(A->bool)->bool`; `s:A->bool`] SUM_SUM_RESTRICT)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC REAL_LE_TRANS `inv(&(SUC n)) * sum (s:A->bool) (\y. &1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_MUL_LINV; REAL_OF_NUM_EQ;
                 NOT_SUC; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s DELETE (y:A)` THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; SUC_SUB1; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A->bool) SUBSET s` MP_TAC THENL
     [ASM_MESON_TAC[]; UNDISCH_TAC `~((y:A) IN x)` THEN SET_TAC[]];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shattered sets and the Vapnik-Chervonenkis dimension of a set system.     *)
(* A set x is shattered by A when its traces {x INTER y | y IN A} are all    *)
(* subsets of x; vc_dimension A is the largest size of a shattered set.      *)
(* ------------------------------------------------------------------------- *)

let shattered = new_definition
 `shattered (A:(A->bool)->bool) =
    {x | {x INTER y | y IN A} = {z | z SUBSET x}}`;;

let vc_dimension = new_definition
 `vc_dimension (A:(A->bool)->bool) =
    @d. (?x. x IN shattered A /\ CARD x = d) /\
        (!x. x IN shattered A ==> CARD x <= d)`;;

let IN_SHATTERED = prove
 (`!(A:(A->bool)->bool) x.
     x IN shattered A <=> !z. z SUBSET x ==> ?y. y IN A /\ x INTER y = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[shattered; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[INTER_SUBSET]);;

let SHATTERED_SUBSET = prove
 (`!s (A:(A->bool)->bool) x.
     (!y. y IN A ==> y SUBSET s) /\ x IN shattered A ==> x SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SHATTERED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:A->bool`)) THEN
  REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[]);;

let FINITE_SHATTERED = prove
 (`!s (A:(A->bool)->bool).
     FINITE s /\ (!x. x IN A ==> x SUBSET s) ==> FINITE(shattered A)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[SHATTERED_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Pajor's inequality: a set system has at most as many members as it        *)
(* shatters sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_SHATTERED = prove
 (`!s (A:(A->bool)->bool).
     FINITE s /\ (!x. x IN A ==> x SUBSET s)
     ==> CARD A <= CARD(shattered A)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [X_GEN_TAC `A:(A->bool)->bool` THEN REWRITE_TAC[SUBSET_EMPTY] THEN
    DISCH_TAC THEN ASM_CASES_TAC `A:(A->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; LE_0] THEN
    TRANS_TAC LE_TRANS `CARD {{}:A->bool}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SING] THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_SHATTERED; SUBSET_EMPTY; INTER_EMPTY] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      MATCH_MP_TAC FINITE_SHATTERED THEN EXISTS_TAC `{}:A->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; SUBSET_EMPTY]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `A:(A->bool)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:A`; `t:A->bool`; `A:(A->bool)->bool`]
    CARD_FAMILY_SPLIT_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `B0 = {x:A->bool | x SUBSET t /\ x IN A}` THEN
  ABBREV_TAC `B1 = {x:A->bool | x SUBSET t /\ (a INSERT x) IN A}` THEN
  SUBGOAL_THEN `!P. FINITE {x:A->bool | x SUBSET t /\ P x}` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:A->bool | x SUBSET t}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(B0:(A->bool)->bool) /\ FINITE(B1:(A->bool)->bool) /\
    (!x. x IN B0 UNION B1 ==> x SUBSET t) /\
    (!x. x IN B0 INTER B1 ==> x SUBSET t)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B0"; "B1"] THEN
    ASM_REWRITE_TAC[IN_UNION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(shattered(B0 UNION B1:(A->bool)->bool)) +
              CARD(shattered(B0 INTER B1:(A->bool)->bool))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`B0:(A->bool)->bool`; `B1:(A->bool)->bool`]
      CARD_UNION_GEN) THEN
    MP_TAC(ISPECL [`B0 INTER B1:(A->bool)->bool`; `B0:(A->bool)->bool`]
      CARD_SUBSET) THEN
    MP_TAC(MATCH_MP (ASSUME
     `!A:(A->bool)->bool. (!x. x IN A ==> x SUBSET t)
                          ==> CARD A <= CARD(shattered A)`)
     (ASSUME `!x:A->bool. x IN B0 UNION B1 ==> x SUBSET t`)) THEN
    MP_TAC(MATCH_MP (ASSUME
     `!A:(A->bool)->bool. (!x. x IN A ==> x SUBSET t)
                          ==> CARD A <= CARD(shattered A)`)
     (ASSUME `!x:A->bool. x IN B0 INTER B1 ==> x SUBSET t`)) THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
  SUBGOAL_THEN
   `(!x:A->bool. x IN shattered({x | x SUBSET t /\ x IN A} UNION
                                {x | x SUBSET t /\ a INSERT x IN A})
                 ==> x SUBSET t) /\
    (!x:A->bool. x IN shattered({x | x SUBSET t /\ x IN A} INTER
                                {x | x SUBSET t /\ a INSERT x IN A})
                 ==> x SUBSET t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SHATTERED_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `CARD(shattered({x | x SUBSET t /\ x IN A} UNION
                   {x | x SUBSET t /\ a INSERT x IN A}) UNION
         IMAGE (\x:A->bool. a INSERT x)
               (shattered({x | x SUBSET t /\ x IN A} INTER
                          {x | x SUBSET t /\ a INSERT x IN A})))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    SUBGOAL_THEN
     `FINITE(shattered({x:A->bool | x SUBSET t /\ x IN A} UNION
                       {x | x SUBSET t /\ a INSERT x IN A})) /\
      FINITE(shattered({x:A->bool | x SUBSET t /\ x IN A} INTER
                       {x | x SUBSET t /\ a INSERT x IN A}))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FINITE_SHATTERED THEN
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand) CARD_UNION (rand w))) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`;
                  IN_IMAGE] THEN
      ASM_MESON_TAC[SUBSET; IN_INSERT];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SET_RULE
     `!a:A x y t. ~(a IN t) /\ x SUBSET t /\ y SUBSET t /\
                  a INSERT x = a INSERT y ==> x = y`];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_SHATTERED THEN EXISTS_TAC `(a:A) INSERT t` THEN
    ASM_REWRITE_TAC[FINITE_INSERT]] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `(x:A->bool) SUBSET t` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC])
  THENL
   [SUBGOAL_THEN `~((a:A) IN x)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC
     `(x:A->bool) IN shattered({x | x SUBSET t /\ x IN A} UNION
                               {x | x SUBSET t /\ a INSERT x IN A})` THEN
    REWRITE_TAC[IN_SHATTERED; IN_UNION; IN_ELIM_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A->bool` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `y:A->bool`; EXISTS_TAC `(a:A) INSERT y`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((a:A) IN x)` THEN UNDISCH_TAC `(x:A->bool) INTER y = z` THEN
    SET_TAC[];
    UNDISCH_TAC
     `(x:A->bool) IN shattered({x | x SUBSET t /\ x IN A} INTER
                               {x | x SUBSET t /\ a INSERT x IN A})` THEN
    REWRITE_TAC[IN_SHATTERED; IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z DELETE (a:A)`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(z:A->bool) SUBSET a INSERT x` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:A->bool) IN A`; `(a:A) INSERT y IN A`; `(y:A->bool) SUBSET t`;
      `~((a:A) IN t)`; `(x:A->bool) SUBSET t`;
      `(x:A->bool) INTER y = z DELETE a`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `(a:A) IN z` THENL
     [EXISTS_TAC `(a:A) INSERT y`; EXISTS_TAC `y:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Sauer-Shelah inequality. The chain holds for every set system A of    *)
(* subsets of a finite set s; for A = {} it holds whatever the value of      *)
(* vc_dimension A.                                                           *)
(* ------------------------------------------------------------------------- *)

let CARD_SUBSETS_CARD_LE = prove
 (`!s:A->bool d.
     FINITE s
     ==> CARD {x | x SUBSET s /\ CARD x <= d} =
         nsum(0..d) (\i. binom(CARD s,i))`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. {x:A->bool | x SUBSET s /\ CARD x = k} =
        {x | x SUBSET s /\ x HAS_SIZE k}`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_SIZE; EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0; LE] THENL
   [ASM_SIMP_TAC[CARD_RESTRICTED_POWERSET]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `{x | P x /\ (Q x \/ R x)} = {x | P x /\ R x} UNION {x | P x /\ Q x}`] THEN
  W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand) CARD_UNION (lhand w))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CARD_RESTRICTED_POWERSET]);;

let CARD_SHATTERED_LE_NSUM_BINOM = prove
 (`!s (A:(A->bool)->bool) d.
     FINITE s /\ (!x. x IN A ==> x SUBSET s) /\
     (!x. x IN shattered A ==> CARD x <= d)
     ==> CARD(shattered A) <= nsum(0..d) (\i. binom(CARD s,i))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM CARD_SUBSETS_CARD_LE] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[SHATTERED_SUBSET];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]]);;

let NSUM_BINOM_LE_POW = prove
 (`!n d. nsum(0..d) (\i. binom(n,i)) <= n EXP d + 1`,
  SUBGOAL_THEN
   `!n d. nsum(0..SUC d) (\i. binom(SUC n,i)) =
          nsum(0..SUC d) (\i. binom(n,i)) + nsum(0..d) (\i. binom(n,i))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[MATCH_MP (SPEC_ALL NSUM_CLAUSES_LEFT)
                         (ARITH_RULE `0 <= SUC d`)] THEN
    REWRITE_TAC[ADD1; NSUM_OFFSET] THEN
    REWRITE_TAC[GSYM ADD1; binom; NSUM_ADD_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. n EXP SUC(SUC k) + n EXP SUC k + 1 <= (n + 1) EXP SUC(SUC k)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[EXP; MULT_CLAUSES; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
      ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [EXP] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [EXP] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(n + 1) * (n EXP SUC (SUC k) + n EXP SUC k + 1)` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[BINOM_0; NSUM_DELTA; IN_NUMSEG; LE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[NSUM_SING_NUMSEG; binom; EXP] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN
  STRUCT_CASES_TAC(SPEC `d:num` num_CASES) THENL
   [REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0; binom; GSYM ONE; BINOM_1;
                EXP_1] THEN
    ARITH_TAC;
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(n EXP SUC(SUC n') + 1) + (n EXP SUC n' + 1)` THEN
    ASM_SIMP_TAC[LE_ADD2] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `n':num`]) THEN
    REWRITE_TAC[ADD1] THEN ARITH_TAC]);;

let VC_DIMENSION = prove
 (`!s (A:(A->bool)->bool).
     FINITE s /\ (!x. x IN A ==> x SUBSET s) /\ ~(A = {})
     ==> (?x. x IN shattered A /\ CARD x = vc_dimension A) /\
         (!x. x IN shattered A ==> CARD x <= vc_dimension A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[vc_dimension] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPEC `\d. ?x:A->bool. x IN shattered A /\ CARD x = d` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[CARD_CLAUSES; IN_SHATTERED; SUBSET_EMPTY; INTER_EMPTY] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    EXISTS_TAC `CARD(s:A->bool)` THEN
    ASM_MESON_TAC[SHATTERED_SUBSET; CARD_SUBSET]]);;

let SAUER_SHELAH_INEQUALITY = prove
 (`!s (A:(A->bool)->bool).
     FINITE s /\ (!x. x IN A ==> x SUBSET s)
     ==> CARD A <= CARD(shattered A) /\
         CARD(shattered A) <= nsum(0..vc_dimension A) (\i. binom(CARD s,i)) /\
         nsum(0..vc_dimension A) (\i. binom(CARD s,i))
         <= CARD s EXP vc_dimension A + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[NSUM_BINOM_LE_POW] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_SHATTERED THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CARD_SHATTERED_LE_NSUM_BINOM THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `A:(A->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[IN_SHATTERED; NOT_IN_EMPTY] THEN MESON_TAC[EMPTY_SUBSET];
    ASM_MESON_TAC[VC_DIMENSION]]);;

(* ------------------------------------------------------------------------- *)
(* Shearer's lemma. If every point of the finite ground set s lies in at     *)
(* least t members of a finite family, then |A|^t is at most the product of  *)
(* the sizes of the traces of A on the members. The family may repeat sets   *)
(* (SHEARER_INEQUALITY_GEN, indexed by k) or be a set of sets                *)
(* (SHEARER_INEQUALITY). The only failing case of the unrestricted form is   *)
(* A = {}, t = 0 with a nonempty family, where 0^0 = 1 > 0.                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The AM-GM inequality over any nonempty finite index set.                  *)
(* ------------------------------------------------------------------------- *)

let AGM_FINITE = prove
 (`!s (a:A->real).
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 <= a i)
     ==> product s a <= (sum s a / &(CARD s)) pow (CARD s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  SUBGOAL_THEN `1 <= CARD(s:A->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0]; ALL_TAC] THEN
  SPEC_TAC(`CARD(s:A->bool)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`f:num->A`; `a:A->real`; `1..n`] PRODUCT_IMAGE) THEN
  MP_TAC(ISPECL [`f:num->A`; `a:A->real`; `1..n`] SUM_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC AGM THEN ASM_REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[]);;

let SHEARER_STEP_POW = prove
 (`!x y r s w t.
     1 <= t /\ &0 <= x /\ &0 <= y /\ &0 <= r /\ &0 <= s /\ r + s <= &1 /\
     &0 <= w /\ x pow t <= w * r pow t /\ y pow t <= w * s pow t
     ==> (x + y) pow t <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z u. &0 <= z /\ &0 <= u /\ u <= &1 /\ z pow t <= w * u pow t
          ==> z pow t <= w`
  (LABEL_TAC "h1") THENL
   [REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `w * u pow t` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_1_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z u. &0 <= z /\ u = &0 /\ z pow t <= w * u pow t ==> z = &0`
  (LABEL_TAC "h2") THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `z pow t <= w * u pow t` THEN
    ASM_REWRITE_TAC[REAL_POW_ZERO] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`z:real`; `t:num`] REAL_POW_LE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `z pow t = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [SUBGOAL_THEN `x = &0` SUBST1_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_LID]] THEN
    USE_THEN "h1" MATCH_MP_TAC THEN EXISTS_TAC `s:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `y = &0` SUBST1_TAC THENL
     [USE_THEN "h2" MATCH_MP_TAC THEN EXISTS_TAC `s:real` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_RID]] THEN
    USE_THEN "h1" MATCH_MP_TAC THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ &0 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x / r) pow t <= w /\ (y / s) pow t <= w` STRIP_ASSUME_TAC
  THENL
   [ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_LDIV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `x = r * x / r /\ y = s * y / s` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x / r /\ &0 <= y / s` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `(x / r) pow t <= w` THEN UNDISCH_TAC `(y / s) pow t <= w` THEN
  SPEC_TAC(`x / r`,`a:real`) THEN SPEC_TAC(`y / s`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN
  DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
   [TRANS_TAC REAL_LE_TRANS `b pow t`;
    TRANS_TAC REAL_LE_TRANS `a pow t`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     ALL_TAC])
  THENL
   [MP_TAC(SPECL [`r:real`; `a:real`; `b:real`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`r + s:real`; `&1`; `b:real`] REAL_LE_RMUL);
    MP_TAC(SPECL [`s:real`; `b:real`; `a:real`] REAL_LE_LMUL) THEN
    MP_TAC(SPECL [`r + s:real`; `&1`; `a:real`] REAL_LE_RMUL)] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

let SHEARER_STEP_PRODUCT = prove
 (`!C M (p:B->real) q c x y t.
     FINITE C /\ M SUBSET C /\ 1 <= t /\ t <= CARD M /\
     (!f. f IN C ==> &0 <= p f /\ &0 <= q f /\ p f <= c f /\ q f <= c f) /\
     (!f. f IN M ==> p f + q f <= c f) /\
     &0 <= x /\ &0 <= y /\ x pow t <= product C p /\ y pow t <= product C q
     ==> (x + y) pow t <= product C c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(M:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:B. f IN M ==> f IN C` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product C (c:B->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_CASES_TAC `?g:B. g IN M /\ c g = &0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `g:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:B) IN C` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:B->real) g = &0 /\ (q:B->real) g = &0`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `!f:B. f IN M ==> p f + q f <= c f` THEN
      DISCH_THEN(MP_TAC o SPEC `g:B`) THEN
      UNDISCH_TAC
       `!f:B. f IN C
              ==> &0 <= p f /\ &0 <= q f /\ p f <= c f /\ q f <= c f` THEN
      DISCH_THEN(MP_TAC o SPEC `g:B`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `product C (p:B->real) = &0 /\ product C (q:B->real) = &0`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0] THEN CONJ_TAC THEN EXISTS_TAC `g:B` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `x pow t = &0 /\ y pow t = &0` MP_TAC THENL
     [MP_TAC(SPECL [`x:real`; `t:num`] REAL_POW_LE) THEN
      MP_TAC(SPECL [`y:real`; `t:num`] REAL_POW_LE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_EQ_0] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_POW_ZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:B. f IN M ==> &0 < c f` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(CARD(M:B->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:B->real z.
      &0 <= z /\ (!f. f IN C ==> &0 <= h f /\ h f <= c f) /\
      z pow t <= product C h
      ==> z pow t <=
          product C c * (sum M (\f. h f / c f) / &(CARD(M:B->bool))) pow t`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!g. product C (g:B->real) = product (C DIFF M) g * product M g`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`g:B->real`; `C DIFF M:B->bool`; `M:B->bool`]
        PRODUCT_UNION) THEN
      ASM_SIMP_TAC[FINITE_DIFF] THEN ANTS_TAC THENL
       [SET_TAC[DISJOINT];
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `product (C DIFF M) (h:B->real) * product M h` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
      MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `product M (h:B->real) = product M c * product M (\f. h f / c f)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `!f:B. f IN M ==> &0 <= h f / c f /\ h f / c f <= &1`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                   REAL_MUL_LID];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `(sum M (\f:B. h f / c f) / &(CARD(M:B->bool))) pow (CARD M)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AGM_FINITE THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `t <= CARD(M:B->bool)` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; SUM_POS_LE; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID] THEN
    TRANS_TAC REAL_LE_TRANS `sum M (\f:B. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC SHEARER_STEP_POW THEN
  MAP_EVERY EXISTS_TAC
   [`sum M (\f:B. p f / c f) / &(CARD(M:B->bool))`;
    `sum M (\f:B. q f / c f) / &(CARD(M:B->bool))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `f:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; GSYM SUM_ADD] THEN
    TRANS_TAC REAL_LE_TRANS `sum M (\f:B. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `f:B` THEN DISCH_TAC THEN
      MP_TAC(SPEC `f:B` (ASSUME `!f:B. f IN M ==> &0 < c f`)) THEN
      MP_TAC(SPEC `f:B` (ASSUME `!f:B. f IN M ==> p f + q f <= c f`)) THEN
      REWRITE_TAC[ASSUME `(f:B) IN M`] THEN DISCH_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&0 < c(f:B)`; REAL_MUL_LID;
               ASSUME `p (f:B) + q f <= c f`];
      ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID; REAL_LE_REFL]];
    USE_THEN "sub" (MATCH_MP_TAC o SPEC `p:B->real`) THEN ASM_SIMP_TAC[];
    USE_THEN "sub" (MATCH_MP_TAC o SPEC `q:B->real`) THEN ASM_SIMP_TAC[]]);;

let SHEARER_STEP_TRACES = prove
 (`!a u (A:(A->bool)->bool) g.
     FINITE A /\ ~(a IN u) /\ (!x. x IN A ==> x SUBSET a INSERT u)
     ==> CARD {g INTER x | x IN {x | x SUBSET u /\ x IN A}}
         <= CARD {g INTER x | x IN A} /\
         CARD {g INTER x | x IN {x | x SUBSET u /\ a INSERT x IN A}}
         <= CARD {g INTER x | x IN A} /\
         (a IN g
          ==> CARD {g INTER x | x IN {x | x SUBSET u /\ x IN A}} +
              CARD {g INTER x | x IN {x | x SUBSET u /\ a INSERT x IN A}}
              <= CARD {g INTER x | x IN A})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
  ABBREV_TAC `A0 = {x:A->bool | x SUBSET u /\ x IN A}` THEN
  ABBREV_TAC `A1 = {x:A->bool | x SUBSET u /\ a INSERT x IN A}` THEN
  SUBGOAL_THEN
   `FINITE(A0:(A->bool)->bool) /\ FINITE(A1:(A->bool)->bool) /\
    (!x. x IN A0 ==> x SUBSET u /\ x IN A) /\
    (!x. x IN A1 ==> x SUBSET u /\ a INSERT x IN A)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A0"; "A1"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `A:(A->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC]
    THENL
     [EXPAND_TAC "A0" THEN SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\x:A->bool. x DELETE a) A` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `x:A->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `(a:A) INSERT x` THEN
      UNDISCH_TAC `(x:A->bool) IN A1` THEN EXPAND_TAC "A1" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((a:A) IN u)` THEN UNDISCH_TAC `(x:A->bool) SUBSET u` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
  SUBGOAL_THEN
   `IMAGE (\x:A->bool. g INTER x) A0 SUBSET IMAGE (\x. g INTER x) A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a IN g
    ==> CARD(IMAGE (\x:A->bool. g INTER x) A0) +
        CARD(IMAGE (\x. g INTER x) A1) <= CARD(IMAGE (\x. g INTER x) A)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `(!z:A->bool. z IN IMAGE (\x. g INTER x) A0 ==> z SUBSET u) /\
      (!z:A->bool. z IN IMAGE (\x. g INTER x) A1 ==> z SUBSET u)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[SET_RULE `x SUBSET u ==> (g:A->bool) INTER x SUBSET u`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `CARD(IMAGE (\y:A->bool. a INSERT y) (IMAGE (\x. g INTER x) A1)) =
      CARD(IMAGE (\x:A->bool. g INTER x) A1)`
    (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
      MAP_EVERY X_GEN_TAC [`y:A->bool`; `z:A->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:A->bool) SUBSET u /\ z SUBSET u` MP_TAC THENL
       [ASM_SIMP_TAC[];
        UNDISCH_TAC `(a:A) INSERT y = a INSERT z` THEN
        UNDISCH_TAC `~((a:A) IN u)` THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (\x:A->bool. g INTER x) A0`;
      `IMAGE (\y:A->bool. (a:A) INSERT y) (IMAGE (\x. g INTER x) A1)`]
     CARD_UNION) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
      X_GEN_TAC `z:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:A->bool` (SUBST_ALL_TAC o CONJUNCT1)) THEN
      SUBGOAL_THEN `(a:A) INSERT y SUBSET u` MP_TAC THENL
       [ASM_SIMP_TAC[]; UNDISCH_TAC `~((a:A) IN u)` THEN SET_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(a:A) INSERT x` THEN
    CONJ_TAC THENL [UNDISCH_TAC `(a:A) IN g` THEN SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSET; FINITE_IMAGE] THEN
  ASM_CASES_TAC `(a:A) IN g` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `(a:A) INSERT x` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `~((a:A) IN g)` THEN SET_TAC[]; ASM_SIMP_TAC[]]);;

let SHEARER_INEQUALITY_REAL = prove
 (`!k (f:B->A->bool) t.
     FINITE k /\ 1 <= t
     ==> !s. FINITE s
             ==> !A:(A->bool)->bool.
                   (!x. x IN A ==> x SUBSET s) /\
                   (!i. i IN s ==> t <= CARD {j | j IN k /\ i IN f j})
                   ==> &(CARD A) pow t <=
                       product k (\j. &(CARD {f j INTER x | x IN A}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [X_GEN_TAC `A:(A->bool)->bool` THEN
    REWRITE_TAC[SUBSET_EMPTY; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_CASES_TAC `A:(A->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[CARD_CLAUSES; REAL_POW_ZERO] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `A:(A->bool)->bool = {{}}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY];
      REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; INTER_EMPTY; CARD_SING;
                  REAL_POW_ONE; PRODUCT_ONE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `u:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `A:(A->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(A:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:A->bool | x SUBSET a INSERT u}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET; FINITE_INSERT] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:A`; `u:A->bool`; `A:(A->bool)->bool`]
    CARD_FAMILY_SPLIT_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  MATCH_MP_TAC SHEARER_STEP_PRODUCT THEN
  EXISTS_TAC `{j:B | j IN k /\ (a:A) IN (f:B->A->bool) j}` THEN
  EXISTS_TAC
   `\j:B. &(CARD {(f:B->A->bool) j INTER x |
                  x IN {x:A->bool | x SUBSET u /\ x IN A}})` THEN
  EXISTS_TAC
   `\j:B. &(CARD {(f:B->A->bool) j INTER x |
                  x IN {x:A->bool | x SUBSET u /\ (a:A) INSERT x IN A}})` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[SUBSET; IN_ELIM_THM];
    MP_TAC(SPEC `a:A` (ASSUME
     `!i:A. i IN a INSERT u
            ==> t <= CARD {j:B | j IN k /\ i IN (f:B->A->bool) j}`)) THEN
    REWRITE_TAC[IN_INSERT];
    X_GEN_TAC `j:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:A`; `u:A->bool`; `A:(A->bool)->bool`;
                   `(f:B->A->bool) j`] SHEARER_STEP_TRACES) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN SIMP_TAC[];
    X_GEN_TAC `j:B` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:A`; `u:A->bool`; `A:(A->bool)->bool`;
                   `(f:B->A->bool) j`] SHEARER_STEP_TRACES) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN SIMP_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [SIMP_TAC[];
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ASSUME
       `!i:A. i IN a INSERT u
              ==> t <= CARD {j:B | j IN k /\ i IN (f:B->A->bool) j}`) THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    USE_THEN "ih" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [SIMP_TAC[];
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ASSUME
       `!i:A. i IN a INSERT u
              ==> t <= CARD {j:B | j IN k /\ i IN (f:B->A->bool) j}`) THEN
      ASM_REWRITE_TAC[IN_INSERT]]]);;

let SHEARER_INEQUALITY_GEN = prove
 (`!s (A:(A->bool)->bool) (f:B->A->bool) k t.
     FINITE s /\ FINITE k /\ (!x. x IN A ==> x SUBSET s) /\
     (!i. i IN s ==> t <= CARD {j | j IN k /\ i IN f j}) /\
     ~(A = {} /\ t = 0 /\ ~(k = {}))
     ==> CARD A EXP t <= nproduct k (\j. CARD {f j INTER x | x IN A})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(A:(A->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:A->bool | x SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [UNDISCH_TAC
     `~((A:(A->bool)->bool) = {} /\ t = 0 /\ ~(k:B->bool = {}))` THEN
    ASM_REWRITE_TAC[EXP; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[NPRODUCT_EQ_0; SIMPLE_IMAGE; CARD_EQ_0; FINITE_IMAGE;
                   IMAGE_EQ_EMPTY];
      ASM_REWRITE_TAC[NPRODUCT_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN
  MP_TAC(SPECL [`k:B->bool`; `f:B->A->bool`; `t:num`]
    SHEARER_INEQUALITY_REAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SHEARER_INEQUALITY = prove
 (`!s (A:(A->bool)->bool) C t.
     FINITE s /\ FINITE C /\ (!x. x IN A ==> x SUBSET s) /\
     (!i. i IN s ==> t <= CARD {c | c IN C /\ i IN c}) /\
     ~(A = {} /\ t = 0 /\ ~(C = {}))
     ==> CARD A EXP t <= nproduct C (\c. CARD {c INTER x | x IN A})`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `A:(A->bool)->bool`; `\c:A->bool. c`;
                 `C:(A->bool)->bool`; `t:num`] SHEARER_INEQUALITY_GEN) THEN
  BETA_TAC THEN REWRITE_TAC[]);;

let SHEARER_INEQUALITY_COUNTEREXAMPLE = prove
 (`~(!n (A:(num->bool)->bool) C t.
       (!x. x IN A ==> x SUBSET 1..n) /\ (!c. c IN C ==> c SUBSET 1..n) /\
       (!i. i IN 1..n ==> t <= CARD {c | c IN C /\ i IN c})
       ==> CARD A EXP t <= nproduct C (\c. CARD {c INTER x | x IN A}))`,
  DISCH_THEN(MP_TAC o SPECL
   [`0`; `{}:(num->bool)->bool`; `{{}:num->bool}`; `0`]) THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_SING; FORALL_UNWIND_THM2; EMPTY_SUBSET;
              LE_0; NPRODUCT_SING; SIMPLE_IMAGE; IMAGE_CLAUSES;
              CARD_CLAUSES; EXP] THEN
  ARITH_TAC);;
