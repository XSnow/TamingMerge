Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Export syntax_ott.
Require Import
        Infrastructure
        SubtypingInversion
        Disjointness.


Create HintDb common.
#[export] Hint Extern 1 (exists _, _) => exists : common.
#[export] Hint Extern 1 => match goal with
                   [ h : exists _ , _ |- _ ] => destruct h
                 end : common.


#[export] Hint Extern 0 => match goal with
                   | [ H: value (e_app _ _) |- _ ] => inverts H
                   | [ H: value (e_fixpoint _ _ ) |- _ ] => inverts H
                   | [ H: prevalue (e_app _ _) |- _ ] => inverts H
                   | [ H: prevalue (e_fixpoint _ _) |- _ ] => inverts H
                 end : falseHd.

Lemma principal_type_checks: forall e A B,
    pType e A -> Typing nil e Inf B -> A = B.
Proof.
  intros e A B H H0. gen B.
  induction H; intros; try solve [inverts* H0].
  - inverts* H0. forwards*: IHpType H3. subst*.
  - inverts H1;
      forwards*: IHpType1;
      forwards*: IHpType2;
      subst*.
Qed.

Lemma prevalue_exists_ptype : forall u,
    prevalue u -> exists A, pType u A.
Proof with eauto with common.
  intros u H.
  induction H... induction H...
Qed.


Lemma typ_value_ptype: forall v A,
    Typing nil v Inf A -> value v -> pType v A.
Proof.
  introv Ht Hv. gen A.
  induction Hv; intros; inverts~ Ht.
Qed.

#[export] Hint Immediate typ_value_ptype : core.

Lemma typ_prevalue_ptype: forall u A,
    Typing nil u Inf A -> prevalue u -> pType u A.
Proof.
  introv Ht Hp. gen A.
  induction Hp; intros; inverts~ Ht; inverts~ H.
Qed.

#[export] Hint Immediate typ_prevalue_ptype : core.

Ltac unify_pType e :=
  match goal with
  | [H1: pType e _, H2: Typing _ e Inf _ |- _] =>
    (forwards: principal_type_checks H1 H2; subst)
  | [H1: prevalue e, H2: Typing _ e Inf _ |- _] =>
    (forwards: typ_prevalue_ptype H2 H1)
  | [H1: value e, H2: Typing _ e Inf _ |- _] =>
    (forwards: typ_value_ptype H2 H1)
  | [H1: prevalue e |- _] =>
    (forwards (?&?): prevalue_exists_ptype H1)
  end.


Lemma prevalue_merge_l_inv : forall u1 u2,
    prevalue (e_merge u1 u2) -> prevalue u1.
Proof.
  intros u1 u2 H.
  inductions H; auto.
  inverts~ H.
Qed.

Lemma prevalue_merge_r_inv : forall u1 u2,
    prevalue (e_merge u1 u2) -> prevalue u2.
Proof.
  intros u1 u2 H.
  inductions H; auto.
  inverts~ H.
Qed.

Lemma prevalue_rcd_inv : forall l u,
    prevalue (e_rcd l u) -> prevalue u.
Proof.
  intros l u  H.
  inductions H; auto.
  inverts~ H.
Qed.

#[export] Hint Immediate prevalue_merge_l_inv prevalue_merge_r_inv prevalue_rcd_inv: core.

(* TypedReduce *)
Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A v' -> value v'.
Proof with eauto with termDb.
  intros v A v' Val Red.
  induction* Red; try solve [inverts* Val]...
Qed.

#[export] Hint Immediate TypedReduce_prv_value : core.

Lemma TypedReduce_top_normal : forall (v v': exp),
    TypedReduce v t_top v' -> v' = e_top.
Proof.
  intros v v' H.
  inductions H;
    solve [inverts* H].
Qed.


Lemma TypedReduce_toplike : forall A v1 v2 v1' v2',
    topLike A -> value v1 -> value v2 -> TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.
Proof with (solve_false; auto).
  assert (HH: forall v v' A, value v -> ord A -> topLike A -> TypedReduce v A v' -> v' = e_top). {
    intros.
    induction H2...
    - inverts~ H. inverts* H1...
    - inverts~ H.
    - inverts~ H.
  }
  intros A v1 v2 v1' v2' TL Val1 Val2 Red1 Red2.
  gen v1' v2'.
  proper_ind A; inverts TL; intros;
    try solve [ (* ordinary *)
          forwards*: HH Val1 Red1;
          forwards*: HH Val2 Red2;
          subst* ];
    try solve [ (* splittable *)
          inverts H;
          inverts Red1; solve_false; auto;
          inverts Red2; solve_false; auto;
          split_unify;
          forwards*: IHr1;
          forwards*: IHr2;
          congruence].
Qed.


Lemma TypedReduce_sub: forall v v' A B,
    value v -> TypedReduce v A v' -> pType v B -> algo_sub B A.
Proof with eauto with common.
  introv Val Red Typ. gen B.
  induction Red; intros.
  - inverts Typ...
  - inverts Typ...
  - inverts Typ...
  - inverts Val.
    inverts Typ.
    forwards*: IHRed...
  - inverts Val.
    inverts Typ...
  - inverts Val.
    inverts Typ...
  - forwards*: IHRed1...
Qed.


(* consistency *)
Definition consistencySpec v1 v2 :=
  forall A v1' v2', ord A -> TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.

#[export] Hint Unfold consistencySpec : core.


Lemma consistent_symm: forall e1 e2,
    consistent e1 e2 -> consistent e2 e1.
Proof with eauto.
  intros e1 e2 H.
  induction H...
Qed.

#[export] Hint Resolve consistent_symm : core.


Lemma consistent_refl: forall v A,
    value v -> Typing nil v Inf A -> consistent v v.
Proof with eauto.
  intros v A H Typ.
  gen A.
  induction H; intros...
  - constructor; constructor;
      inverts Typ;
      forwards* (?&?): prevalue_exists_ptype v1;
      forwards* (?&?): prevalue_exists_ptype v2;
      forwards* : principal_type_checks v1;
      forwards* : principal_type_checks v2; subst...
  - inverts* Typ.
Qed.


#[export] Hint Resolve consistent_refl : core.
