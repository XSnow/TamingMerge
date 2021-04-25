Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        KeyProperties
        SubtypingInversion
        Disjointness
        Deterministic
        Progress.

Require Import Arith Lia.


#[export]
Hint Extern 0 => match goal with
                   | [ H1: ~topLike ?A, H2: topLike (t_rcd _ ?A) |- _ ] => (exfalso; apply H1; inverts H2)
                 end : falseHd.


Theorem consistent_sound: forall v1 v2 A B,
    value v1 -> value v2 ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B ->
    consistent v1 v2 -> consistencySpec v1 v2.
Proof.
  intros v1 v2 A B Val1 Val2 Typ1 Typ2 Cons.
  unfolds. intros C v1' v2' Ord R1 R2.
  forwards*: TypedReduce_unique Cons.
Qed.


Lemma consistent_mergel: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistent (e_merge v1 v2) v -> consistent v1 v /\ consistent v2 v.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  inductions H.
  -
    inverts H.
    lets* (?&?): disjoint_splitl H1.
  - split; eauto.
  - forwards (?&?): IHconsistent1; try reflexivity; auto.
    forwards (?&?): IHconsistent2; try reflexivity; auto.
Qed.

Lemma consistent_merger: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistent v (e_merge v1 v2) -> consistent v v1 /\ consistent v v2.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  inductions H.
  -
    inverts H0.
    lets* (?&?): disjoint_splitr H1.
  - forwards (?&?): IHconsistent1; try reflexivity; auto.
    forwards (?&?): IHconsistent2; try reflexivity; auto.
  - split; eauto.
Qed.


Lemma consistencySpec_mergel: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistencySpec (e_merge v1 v2) v -> consistencySpec v1 v /\ consistencySpec v2 v.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  split; unfolds; intros.
  - forwards*: H A.
  - forwards*: H A.
Qed.

Lemma consistencySpec_merger: forall v1 v2 v,
    lc_exp v1 -> lc_exp v2 -> consistencySpec v (e_merge v1 v2) -> consistencySpec v v1 /\ consistencySpec v v2.
Proof.
  intros v1 v2 v Lc1 Lc2 H.
  split; unfolds; intros.
  - forwards*: H A.
  - forwards*: H A.
Qed.

Lemma topLike_disjoint: forall A B,
    topLike A -> disjointSpec A B.
Proof.
  intros A B H.
  unfolds. intros C H0 H1.
  apply topLike_super_top in H.
  apply topLike_super_top.
  auto_sub.
Qed.


Lemma disjoint_or_exists: forall A B,
    disjoint A B \/ exists C, ord C /\ algo_sub A C /\ algo_sub B C /\ ~ topLike C.
Proof with solve_false.
  intros A B. gen B.
  induction A; intros; auto.
  - induction B; auto.
    + right. exists t_int.
      repeat split~...
    + lets [?|(?&?&?&?&?)]: IHB1.
      * lets [?|(?&?&?&?&?)]: IHB2.
        ** left*.
        ** right. exists* x.
      * right. exists* x.
  - clear IHA1.
    induction B; auto.
    + clear IHB1 IHB2.
      lets [?|(?&?&?&?&?)]: (IHA2 B2); jauto.
      * right. exists* (t_arrow (t_and A1 B1) x).
    + lets [?|(?&?&?&?&?)]: IHB1.
      * lets [?|(?&?&?&?&?)]: IHB2; auto.
        ** right. exists* x.
      * right. exists* x.
  - lets [?|(?&?&?&?&?)]: IHA1.
    lets [?|(?&?&?&?&?)]: IHA2.
    * left*.
    * right. exists* x.
    * right. exists* x.
  - (* rcd *)
    induction~ B.
    + lets [?|(?&?&?&?&?)]: IHB1.
      * lets [?|(?&?&?&?&?)]: IHB2; auto.
        ** right. exists* x.
      * right. exists* x.
    + destruct* (l == l0). subst.
      lets~ [?|(?&?&?&?&?)]: (IHA B).
      right. exists (t_rcd l0 x). splits*.
      intros HF. apply H2. inverts~ HF.
Qed.

Lemma consistencySpec_lams_inv : forall T1 T2 e1 e2 A1 A2 B1 B2,
    Typing nil (e_abs A1 e1 B1) Inf T1 -> Typing nil (e_abs A2 e2 B2) Inf T2 ->
    consistencySpec (e_abs A1 e1 B1) (e_abs A2 e2 B2) -> disjoint B1 B2 \/ (e1=e2) /\ (A1=A2).
Proof.
  introv Typ1 Typ2 Cons.
  inverts keep Typ1. inverts keep Typ2.
  lets~ [?|(?&?&?&?&?)]: disjoint_or_exists B1 B2.
  right.
  assert (S1: algo_sub (t_arrow A1 B1) (t_arrow (t_and A1 A2) x)) by auto_sub.
  assert (S2: algo_sub (t_arrow A2 B2) (t_arrow (t_and A1 A2) x)) by auto_sub.
  forwards~ T1: Typ_sub Typ1 S1.
  forwards~ T2: Typ_sub Typ2 S2.
  forwards* (?&R1) : TypedReduce_progress T1.
  forwards* (?&R2) : TypedReduce_progress T2.
  forwards~ : Cons R1 R2.
  inverts keep R1; inverts keep R2; solve_false.
  (* TEMP0 : e_abs A0 e0 x = e_abs A e x *)
  inverts~ TEMP0.
Qed.

Lemma consistencySpec_rcd_inv : forall T1 T2 l v1 v2,
    value v1 -> value v2 -> nil ⊢ v1 ⇒ T1 -> nil ⊢ v2 ⇒ T2 ->
    consistencySpec (e_rcd l v1) (e_rcd l v2) -> consistencySpec v1 v2.
Proof.
  intros T1 T2 l v1 v2 Val1 Val2 Typ1 Typ2 Cons.
  unfolds. introv Ord R1 R2.
  destruct (toplike_decidable A).
  - forwards~: TypedReduce_toplike R1 R2.
  - forwards*: Cons (t_rcd l A).
    inversion~ H0.
Qed.

Ltac indExpSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

Theorem consistent_complete: forall v1 v2 A B,
    value v1 -> value v2 ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B ->
    consistencySpec v1 v2 -> consistent v1 v2.
Proof with (simpl; try lia; auto).
  intros v1 v2 A B Val1 Val2 Typ1 Typ2 Cons. gen Val1 Val2 Cons A B.
  indExpSize (size_exp v1 + size_exp v2);
  inverts Val1 as V1_1 V1_2; inverts Val2 as V2_1 V2_2; simpl in SizeInd;
    try solve [
          inverts Typ1 as T1_1 T1_2; inverts Typ2 as T2_1 T2_2;
            match goal with
            | |- consistent (e_merge _ _) _ =>
              ( lets~ (C1&C2): consistencySpec_mergel Cons;
                forwards*: IH C1; simpl; try lia; auto;
                try forwards*: IH C2; simpl; try lia; auto
              )
            | |- consistent _ (e_merge _ _) =>
              ( lets~ (C1&C2): consistencySpec_merger Cons;
                forwards*: IH C1; simpl; try lia; auto;
                try forwards*: IH C2; simpl; try lia; auto
              )
            | _ =>
              ( applys C_disjoint; constructor* )
            end].
  - (* lit *)
    inverts keep Typ1; inverts keep Typ2.
    enough (i5=i0).
    subst~.
    forwards* (?&R1) : TypedReduce_progress (e_lit i0).
    forwards* (?&R2) : TypedReduce_progress (e_lit i5).
    forwards*: TypedReduce_unique R1.
    forwards*: TypedReduce_unique R2.
    forwards*: Cons. subst*. congruence.
  - (* abs *)
    forwards* [?|(?&?)]: consistencySpec_lams_inv Cons.
    + applys* C_disjoint.
    + subst*.
  - (* rcd *)
    inverts keep Typ1; inverts keep Typ2.
    destruct (l0==l1).
    + subst*.
      forwards~ Con': consistencySpec_rcd_inv H1 H2 Cons.
      forwards*: IH Con'...
    + applys C_disjoint; constructor*.
Qed.


Lemma consistent_lams_inv : forall T1 T2 e1 e2 A1 A2 B1 B2,
    Typing nil (e_abs A1 e1 B1) Inf T1 -> Typing nil (e_abs A2 e2 B2) Inf T2 ->
    consistent (e_abs A1 e1 B1) (e_abs A2 e2 B2) -> disjoint B1 B2 \/ (e1=e2) /\ (A1=A2).
Proof.
  introv Typ1 Typ2 Cons.
  eapply consistent_sound in Cons; eauto.
  forwards* : consistencySpec_lams_inv Cons.
Qed.

Lemma consistent_rcd_inv : forall l v1 v2,
    consistent (e_rcd l v1) (e_rcd l v2) -> consistent v1 v2.
Proof.
  intros l v1 v2 H.
  inverts~ H.
  - inverts H0. inverts H1.
    enough (Dis: disjoint A0 A).
    applys* C_disjoint Dis. eauto.
Qed.

#[export]
Hint Immediate consistent_rcd_inv : core.
