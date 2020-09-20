Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Key_Properties
        Subtyping_inversion
        Disjoint_n_toplike
        Deterministic
        Progress
        Consistency.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


(* requires sub Top A -> toplike A *)
Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A v1 -> TypedReduce v1 B v2 -> TypedReduce v B v2.
Proof with eauto.
  introv Val Red1 Red2. gen B v2.
  induction* Red1; introv Red2; inductions Red2...
  inverts* Val.
Qed.


Lemma consistent_afterTR : forall v A B C v1 v2,
    value v -> Typing nil v Inf C -> TypedReduce v A v1 -> TypedReduce v B v2 -> consistencySpec v1 v2.
Proof.
  unfold consistencySpec. introv Val Typ Red1 Red2 Ord Red1' Red2'.
  forwards* r1: TypedReduce_trans Red1 Red1'. forwards* r2: TypedReduce_trans Red2 Red2'.
  forwards*: TypedReduce_unique r1 r2.
Qed.


Lemma TypedReduce_preservation: forall v v' A B,
    value v -> TypedReduce v A v'-> Typing nil v Inf B -> exists C, pType v' C /\ Typing nil v' Inf C /\ subsub C A.
Proof with eauto.
  introv Val Red Typ. (* '. forwards* (B&Typ&Sub): Typing_chk2inf Typ'. *)
  gen B. lets Red': Red.
  induction Red; intros; try solve [jauto].
  - Case "absv".
    simpl. exists. splits*.
    inverts Typ. applys Typ_abs. intros. apply~ Typing_chk_sub.
  - Case "rcd".
    inverts Val. inverts Typ; forwards* (?&?&?&?): IHRed.
    exists* (t_rcd l x).
  - Case "mergel".
    inverts Val. inverts Typ; forwards*: IHRed.
  - Case "merger".
    inverts Val. inverts Typ; forwards*: IHRed.
  - Case "merge_and".
    forwards (?&?&?&?): IHRed1 Val Red1 Typ.
    forwards (?&?&?&?): IHRed2 Val Red2 Typ.
    lets Con: consistent_afterTR Val Typ Red1 Red2.
    eapply consistent_complete in Con...
    exists. splits*.
Qed.


Lemma TypedReduce_consistent : forall v A B C v1 v2,
    value v -> Typing nil v Inf C -> TypedReduce v A v1 -> TypedReduce v B v2 -> consistent v1 v2.
Proof with eauto.
  intros v A B C v1 v2 Val Typ Red1 Red2.
  forwards* (?&?&?&?): TypedReduce_preservation Red1.
  forwards* (?&?&?&?): TypedReduce_preservation Red2.
  forwards*: TypedReduce_prv_value Red1.
  forwards*: TypedReduce_prv_value Red2.
  apply~ consistent_complete...
  forwards*: consistent_afterTR Red1 Red2.
Qed.



Lemma papp_consistent : forall v1 v2 v e1 e2 A B C,
    value v1 -> value v2 -> value v ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B -> Typing nil v Inf C ->
    papp v1 (vl_exp v) e1 -> papp v2 (vl_exp v) e2 -> consistent v1 v2 -> consistent e1 e2.
Proof with (solve_false; eauto).
  introv Val1 Val2 Val3 Typ1 Typ2 Typ3 P1 P2 Cons.
  gen A B C. lets P1': P1. lets P2': P2.
  inductions P1; inductions P2; intros; try solve [applys* C_disjoint].
  - forwards* [?|(?&?)]: consistent_lams_inv Cons.
    + applys* C_disjoint.
    + subst. forwards*: TypedReduce_unique H0 H2.
      subst*.
  - lets* (?&?): consistent_merger Cons. inverts* Typ2.
  - lets* (?&?): consistent_merger Cons. inverts* Typ2.
  - lets* (?&?): consistent_mergel Cons. inverts* Typ1.
  - lets* (?&?): consistent_mergel Cons. inverts* Typ1.
  - (* merge ~ merge *)
    inverts Val1. lets~ (?&?): consistent_mergel Cons.
    inverts* Typ1.
Qed.


Lemma papp_consistent2 : forall v1 v2 l e1 e2 A B,
    value v1 -> value v2 ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B ->
    papp v1 (vl_la l) e1 -> papp v2 (vl_la l) e2 -> consistent v1 v2 -> consistent e1 e2.
Proof with (solve_false; eauto).
  introv Val1 Val2 Typ1 Typ2 P1 P2 Cons.
  gen A B. lets P1': P1. lets P2': P2.
  inductions P1; inductions P2; intros;
    try solve [applys* C_disjoint];
    try solve [inverts Val1; inverts Typ1; applys* C_disjoint];
    try solve [inverts Val2; inverts Typ2; applys* C_disjoint];
    try solve [lets* (?&?): consistent_mergel Cons; inverts* Typ1];
    try solve [lets* (?&?): consistent_merger Cons; inverts* Typ2].
  - inverts Cons.
    + inverts P1'. inverts P2'. subst*.
    + enough (consistent (e_rcd l v) (e_rcd l v0)). eauto.
      applys* C_disjoint H3.
Qed.


Lemma papp_preservation : forall v1 v2 e A,
    value v1 -> value v2 ->
    Typing nil (e_app v1 v2) Inf A ->
    papp v1 (vl_exp v2) e ->
    Typing nil e Inf A.
Proof with eauto.
  intros v1 v2 e A Val1 Val2 Typ P. gen A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3.
  - (* abs *)
    forwards* (T & Htyp & Hsub): Typing_chk2inf Typ3.
    forwards (? & p1 & p2 & p3): TypedReduce_preservation Htyp...
    inverts Typ1 as t1. inverts Typ2.
    eapply Typ_anno. pick fresh y. rewrite (@subst_exp_intro y)...
    forwards~ t1': (t1 y). rewrite_env([]++[(y,B0)]++ []) in t1'.
    lets~ (?&s1&s2): Typing_subst_2 t1' p2 p3.
    apply subsub2sub in s2. forwards*: Typing_chk_sub s2.
  - (* top *)
    inverts Typ1. inverts* Typ2.
  - (* merge *)
    forwards* (T & Htyp & Hsub): Typing_chk2inf Typ3.
    inverts Val1.
    inverts Typ1; inverts Typ2;
      assert (sub (t_and A2 B2) A2) by auto_sub;
      assert (sub (t_and A2 B2) B2) by auto_sub;
      forwards~: IHP1 v2; [ applys* Typ_app H7 | auto | applys* Typ_app H8 | auto ];
      forwards~: IHP2 v2; [ applys* Typ_app H9 | auto | applys* Typ_app H10 | auto ].
    + apply~ Typ_merge. applys* arrTyp_arr_disjoint H6.
    + apply~ Typ_mergev. applys* papp_consistent P1 P2.
Qed.


Lemma papp_preservation2 : forall v1 l e A,
    value v1 ->
    Typing nil (e_proj v1 l) Inf A ->
    papp v1 (vl_la l) e ->
    Typing nil e Inf A.
Proof with eauto.
  intros v1 l e A Val1 Typ P. gen A.
  inductions P; intros; inverts Typ as Typ1 Typ2 Typ3.
  - (* rcd *)
    inverts Typ1. inverts* Typ2.
  - (* top *)
    inverts Typ1. inverts* Typ2.
  - (* merge *)
    inverts Val1.
    inverts Typ1; inverts Typ2;
      forwards~: IHP1 l; [ applys* Typ_proj H7 | auto | applys* Typ_proj H8 | auto ];
      forwards~: IHP2 l; [ applys* Typ_proj H9 | auto | applys* Typ_proj H10 | auto ].
    + apply~ Typ_merge. applys* arrTyp_rcd_disjoint H6.
    + apply~ Typ_mergev. applys* papp_consistent2 P1 P2.
Qed.

Inductive step_or_v : exp -> exp -> Prop :=
| ST_v : forall v, value v -> step_or_v v v
| ST_s : forall e1 e2, step e1 e2 -> step_or_v e1 e2.

Hint Constructors step_or_v : core.

(* to prove the consistent merge case in preservation_subsub *)
Lemma consistent_steps: forall e1 e2 e1' e2' A B,
    Typing [] e1 Inf A -> Typing [] e2 Inf B ->
    step_or_v e1 e1' -> step_or_v e2 e2' -> consistent e1 e2 ->
    (forall (e e' : exp) (A : typ),
         size_exp e < (size_exp e1 + size_exp e2) -> Typing [] e Inf A -> step e e' -> exists C, [] ⊢ e' ⇒ C /\ subsub C A) ->
    consistent e1' e2'.
Proof with (simpl; omega).
  introv Typ1 Typ2 ST1 ST2 Cons IH. gen e1' e2' A B.
  induction Cons; intros; try solve [inverts ST1; inverts ST2; solve_false; eauto].
    + (* e:A ~ e:B *)
      inverts ST1 as ST1'; inverts ST2 as ST2'; solve_false; eauto.
      inverts Typ1 as H_check_e. inverts H_check_e as H_inf_e.
      inverts ST1' as Hv1 Hs1; inverts ST2' as Hv2 Hs2; solve_false.
      * forwards*: TypedReduce_consistent Hs1 Hs2.
      * forwards*: step_unique Hv1 Hv2. subst*.
    + (* rcd *)
      inverts keep Typ1. inverts keep Typ2.
      inverts ST1 as ST1'; inverts ST2 as ST2'; solve_false; eauto;
        inverts ST1' as Hv1 Hs1; inverts ST2' as Hv2 Hs2; solve_false.
      * (* value VS step *)
        applys C_rcd. applys* IHCons. intros.
        forwards* (?&?&?): IH H3. simpl. omega.
      * (* step VS value *)
        applys C_rcd. applys* IHCons. intros.
        forwards* (?&?&?): IH H3. simpl. omega.
      * (* step VS step *)
        applys C_rcd. applys* IHCons. intros.
        forwards* (?&?&?): IH H3. simpl. omega.
    + (* disjoint *)
      inverts ST1 as ST1'; [unify_pType e1' | unify_pType u1];
        inverts ST2 as ST2'; try unify_pType e2'; try unify_pType u2.
      * (* value VS value *)
        applys* C_disjoint.
      * (* value VS step *)
        forwards* (?&?&?): IH u2. assert (size_exp e1' >0) by eomg. omega.
        forwards~: step_prv_prevalue ST2'. unify_pType e2'.
        applys* C_disjoint.
      * (* step VS value *)
        forwards* (?&?&?): IH u1. assert (size_exp e2' >0) by eomg. omega.
        forwards~: step_prv_prevalue ST1'. unify_pType e1'.
        applys* C_disjoint.
      * (* step VS step *)
        forwards* (?&?&?): IH u1. assert (size_exp u2 >0) by eomg. omega.
        forwards* (?&?&?): IH u2. assert (size_exp u1 >0) by eomg. omega.
        forwards~: step_prv_prevalue ST1'. unify_pType e1'.
        forwards~: step_prv_prevalue ST2'. unify_pType e2'.
        applys* C_disjoint.
    + (* merge on left *)
      inverts ST1 as ST1'; [ | inverts ST1' as ST1_1 ST1_2 ]; inverts Typ1;
        try solve [
              forwards*: IHCons1; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; omega);
              forwards*: IHCons2; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; omega)].
    + (* merge on right *)
      inverts ST2 as ST2'; [ | inverts ST2' as ST2_1 ST2_2 ]; inverts Typ2;
        try solve [
              forwards*: IHCons1; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; omega);
              forwards*: IHCons2; try introv p1 p2 p3; try applys~ IH p2 p3; try (simpl; omega)].
Qed.

Ltac indExpDirSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : dirflag |- _ ] => (gen h) end;
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

Definition size_dir dir :=
  match dir with
  | Inf => 0
  | Chk => 1
  end.


Theorem preservation_subsub : forall e e' dir A,
    Typing nil e dir A ->
    step e e' ->
    exists C, Typing nil e' dir C /\ subsub C A.
Proof with (simpl; try omega; auto; try eassumption; auto).
  introv Typ J. gen A e'.
  indExpDirSize ((size_exp e) + (size_dir dir)).
  inverts keep Typ as Ht1 Ht2 Ht3 Ht4;
    try solve [inverts J]; repeat simpl in SizeInd.
  - Case "typing_app".
    inverts J as J1 J2 J3; try forwards* (?&?&S2): IH J2; assert (size_exp e1 >0) by eomg; eomg.
    + forwards*: papp_preservation J3.
    + lets* ( ?&? & Harr & Hsub ): arrTyp_arr_subsub Ht2 S2.
    forwards* (?&?): subsub_arr_inv Hsub.
    + exists. split*. applys* Typ_app Ht2. applys* Typing_chk_sub.
  - Case "typing_proj".
    inverts J as J1 J2 J3; try forwards* (?&?&S2): IH J1; eomg.
    + forwards*: papp_preservation2 J2.
    + lets* ( ? & Harr & Hsub ): arrTyp_rcd_subsub Ht2 S2.
      forwards* (?&?): subsub_rcd_inv Hsub.
  - Case "typing_rcd".
    (* disjoint *)
    inverts J as J1 J2 J3;
    try forwards* (?&?&?): IH J1; eomg;
    try forwards* (?&?&?): IH J2; eomg.
  - Case "typing_merge".
    (* disjoint *)
    inverts J as J1 J2 J3;
    try forwards* (?&?&?): IH J1; eomg;
    try forwards* (?&?&?): IH J2; eomg.
  - Case "typing_anno".
    inverts Ht1. inverts J as J1 J2 J3.
    + lets* (?&?): TypedReduce_preservation J2.
    + forwards* (?&?&?): IH J1...
      exists A. split*. apply subsub2sub in H2.
      assert (sub x A) by auto_sub. lets*: Typ_sub.
  - Case "typing_fix".
    inverts J as Lc. pick_fresh x.
    rewrite* (@subst_exp_intro x).
    forwards~ Typ_chk: Ht1.
    rewrite_env(nil++[(x,A)]++nil) in Typ_chk.
    lets~ (?&?&?): Typing_subst_2 Typ_chk Typ.
    apply subsub2sub in H0. forwards*: Typing_chk_sub H H0.
  - Case "typing_mergev". (* consistent merge *)
    inverts J as J1 J2 J3; forwards*: consistent_steps Ht4;
      (* consistent e1' e2' *)
      try introv p1 p2 p3; try forwards* (?&?&?): IH p2 p3; eomg;
        (* typing for the two terms *)
        try forwards* (?&?&?): IH J1; eomg; try forwards* (?&?&?): IH J2; eomg.
  - Case "subsumption".
    forwards* (?&?&?): IH J...
    apply subsub2sub in H0. assert (sub x A) by auto_sub.
    exists* A.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e e' ->
    Typing nil e' Chk A.
Proof.
  intros e e' dir A H H0.
  lets* (?&?&?): preservation_subsub H H0.
  apply subsub2sub in H2.
  destruct dir.
  - sapply* Typ_sub.
  - sapply* Typing_chk_sub.
Qed.


(* Type Safety *)
Theorem preservation_multi_step : forall e e' dir A,
    Typing nil e dir A ->
    e ->* e' ->
    exists C, Typing nil e' dir C /\ subsub C A.
Proof.
  introv Typ Red.
  gen A. induction* Red.
  intros.
  lets* (?&?&?): preservation_subsub Typ H.
  forwards* (?&?&?): IHRed H0.
  exists x0. split*.
  forwards*: subsub_trans H3 H1.
Qed.


Theorem type_safety : forall e e' dir A,
    Typing nil e dir A ->
    e ->* e' ->
    value e' \/ exists e'', step e' e''.
Proof.
  introv Typ Red. gen A.
  induction Red; intros.
  lets*: progress Typ.
  lets* (?&?&?): preservation_subsub Typ H.
Qed.
