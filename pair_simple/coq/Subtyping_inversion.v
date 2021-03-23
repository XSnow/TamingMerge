Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import syntax_ott
               rules_inf.
Require Import Omega.
Require Import Program.Equality.



Ltac solve_false := try intro; solve [false; eauto with falseHd].


Lemma ord_and_inv : forall A B,
    ord (t_and A B) -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma toplike_int_inv :
    topLike t_int -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma toplike_arrow_inv : forall A B,
    topLike (t_arrow A B) -> topLike B.
Proof.
  introv H.
  inverts~ H.
Qed.

Hint Resolve ord_and_inv toplike_int_inv toplike_arrow_inv : falseHd.



Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub t_top B2 \/ (sub B1 A1 /\ sub A2 B2).
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_inversion_andl_ordr : forall A1 A2 B,
   ord B ->  sub (t_and A1 A2) B -> sub A1 B \/ sub A2 B.
Proof.
  intros.
  inverts* H0; try solve [inverts H].
Qed.

Lemma sub_inversion_toparr : forall B C,
    sub t_top B -> sub B C -> sub t_top C.
Proof.
  intros B C S1 S2.
  gen C.
  remember (t_top).
  induction S1;
    inverts* Heqt;
    intros C S2.
  - intuition eauto.
    remember (t_arrow B1 B2).
    induction S2;
      inverts* Heqt.
  - intuition eauto.
    remember (t_prod B1 B2).
    induction S2;
      inverts* Heqt.
  - intuition eauto.
    remember (t_and A2 A3).
    induction S2;
      inverts* Heqt.
Qed.



Lemma sub_reflexivity : forall A,
    sub A A.
Proof.
  intros A.
  induction* A.
Qed.


Hint Constructors sub : core.

Lemma and_inversion : forall A B C,
    sub A (t_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  dependent induction H; eauto.
  lets*: IHsub B C.
  lets*: IHsub B C.
Qed.

Lemma sub_transtivity : forall B A,
      sub A B -> forall C, sub B C -> sub A C.
Proof.
  induction B;
    intros;
    eauto;
    try solve [dependent induction H0;
               eauto].
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
  - apply and_inversion in H.
    destruct H.
    dependent induction H0; eauto.
  - dependent induction H0; eauto.
    clear IHsub1 IHsub2.
    dependent induction H; eauto.
Qed.

(* topLike *)
Lemma toplike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof.
  intro A.
  split.
  - intro H.
    induction* H.
  - intro H.
    induction A;
      try solve [inverts* H].
Qed.


Lemma sub_inversion_prod_arrr : forall A1 A2 B1 B2,
    sub (t_prod A1 A2) (t_arrow B1 B2) -> topLike B2.
Proof.
  intros.
  inverts* H.
  applys~ toplike_super_top.
Qed.


Ltac auto_sub :=
  auto;
  try match goal with
      | [ |- sub ?A ?A ] => apply sub_reflexivity
      | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?B ] => (
        eapply sub_transtivity;
        try apply H;
        try apply S_andl1;
        try apply sub_reflexivity)
      | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?C ] => (
        try eapply sub_transtivity;
        try apply H;
        try apply S_andl2;
        try apply sub_reflexivity)
      | [ H: sub t_top ?A |- sub _ ?A ] =>
        (applys sub_transtivity H; auto)
      | [ H: topLike ?A |- sub _ ?A ] =>
        (apply toplike_super_top in H; applys sub_transtivity H; auto)
      | [ H: topLike ?A |- sub _ (t_arrow _ ?A) ] =>
        (apply TL_arr in H; apply S_top; auto)
      | [ H: sub (t_arrow _ _) (t_arrow _ _) |- sub _ _ ] => (apply sub_inversion_arrow in H; destruct H; auto_sub)
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
    | |- _ => try constructor*
      end.


Lemma toplike_sub: forall A B,
    topLike A -> sub A B -> topLike B.
Proof.
  intros A B H H0.
  apply toplike_super_top in H.
  apply toplike_super_top.
  auto_sub.
Qed.


Lemma toplike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof.
  induction A.
  - right.
    unfold not.
    intros H.
    inversion H.
  - left*.
  - destruct IHA2.
    + left*.
    + right.
      intros H0. inverts~ H0.
  - destruct IHA1.
    + destruct IHA2.
      * left*.
      * right.
        intros H1. inverts~ H1.
    + right.
      intros H0. inverts~ H0.
  - destruct* IHA1.
    destruct* IHA2.
    * right.
      intros H1. inverts~ H1.
    * right.
      intros H1. inverts~ H1.
Qed.

(* disjoint *)
Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - gen B.
    induction A;
      introv H;
      induction B;
      try solve [constructor*].
    + (* int int *)
      assert (~topLike t_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards: (H t_int); auto_sub.
      contradiction.
    + (* arr arr *)
      constructor.
      clear IHA1 IHB1.
      apply IHA2.
      intros.
      remember (t_arrow (t_and A1 B1) C).
      assert (TL: topLike t). {
        apply H;
          subst;
          constructor*;
          [apply S_andl1 | apply S_andl2];
          auto_sub.
      }
      subst.
      inverts* TL.
    + (* prod prod *)
      constructor*.
      * applys IHA1. intros.
        assert (topLike (t_prod C t_top)) by applys~ H.
        inverts~ H2.
      * applys IHA2. intros.
        assert (topLike (t_prod t_top C)) by applys~ H.
        inverts~ H2.
  - intros H C S1 S2.
    apply toplike_super_top.
    gen B C.
    induction* A;
      intros B H;
      [ induction* B | induction* B | skip  | skip ];
      intros C S1 S2;
      try solve [inverts H].
    + (* int arr *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* int and *)
      induction* C;
      inverts H;
      inverts* S1;
      try solve [
        inverts S2;
        [ forwards*: IHB1 |
          forwards*: IHB2 ]
          ].
      assert (T1 : sub (t_and B1 B2) C1) by auto_sub.
      forwards*: IHC1 T1.
      assert (T2 : sub (t_and B1 B2) C2) by auto_sub.
      forwards*: IHC2 T2.
    + (* prod int *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* arr int *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* arr arr *)
      inverts H.
      induction* C;
        inverts S1;
        inverts* S2.
    + (* arr and *)
      induction* C;
      inverts* H;
      inverts* S1.
      *
        inverts S2;
        forwards*: IHB1.
      *
      assert (T1 : sub (t_and B1 B2) C1) by auto_sub.
      forwards*: IHC1 T1.
      assert (T2 : sub (t_and B1 B2) C2) by auto_sub.
      forwards*: IHC2 T2.
    + (* arr prod *)
      induction* C;
        inverts S1;
        inverts* S2.
Qed.


Lemma disjoint_and: forall A B C,
    disjointSpec (t_and B C) A <-> disjointSpec B A /\ disjointSpec C A.
Proof.
  split;
  intro H.
  - apply disjoint_eqv in H.
    split;
      apply disjoint_eqv;
      induction A;
      invert* H.
  - destruct H.
    apply disjoint_eqv in H.
    apply disjoint_eqv in H0.
    apply disjoint_eqv.
    induction* A.
Qed.


Lemma disjoint_and2: forall A B C,
    disjoint (t_and B C) A <-> disjoint B A /\ disjoint C A.
Proof.
  split;
  intro H.
  -
    split;
      induction A;
      invert* H.
  - destruct H.
    induction* A.
Qed.

Lemma disjoint_symmetric: forall A B,
    disjointSpec A B -> disjointSpec B A.
Proof.
  intros A B H.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  forwards*: H.
Qed.

Lemma disjoint_symmetric2: forall A B,
    disjoint A B -> disjoint B A.
Proof.
  intros A B H.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  forwards*: H.
Qed.


(* sub *)
Lemma sub_inversion_arrow_r : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub A2 B2.
Proof.
  intros.
  apply sub_inversion_arrow in H.
  inverts* H.
  apply~ (sub_transtivity t_top); auto_sub.
Qed.


Lemma sub_inversion_arrow_l : forall A1 A2 B1 B2,
    ~ topLike B2 -> sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub B1 A1.
Proof.
  intros.
  apply sub_inversion_arrow in H0.
  inverts* H0.
  - exfalso.
    apply H.
    apply toplike_super_top; auto.
Qed.


Lemma disjoint_domain_type: forall A B C B',
    disjointSpec (t_arrow B C) A -> disjointSpec (t_arrow B' C) A.
Proof.
  intros A B C B' H.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  induction* A;
    invert* H.
Qed.


(* subsub *)
Lemma subsub2sub : forall A B,
    subsub A B -> sub A B.
Proof.
  intros A B H.
  induction H; auto;
    auto_sub.
Qed.

Lemma subsub_trans : forall A B C,
    subsub A B -> subsub B C -> subsub A C.
Proof.
  intros A B C S1 S2.
  gen A C.
  induction B; intros;
    try solve [inductions S1; auto; try solve_false];
    try solve [inductions S1; inverts* S2].
  - (* arrow *)
    inverts~ S1; inverts~ S2; try solve_false.
    + (* arr  *)
      forwards~: IHB2.
      lets~: sub_transtivity H1 H2.
    + (* toplike *)
      inverts H.
      apply subsub2sub in H4.
      lets~: sub_transtivity H3 H4.
  - (* and *)
    inverts~ S1; inverts~ S2; try solve_false.
    inverts H.
    apply subsub2sub in H2. apply subsub2sub in H4.
    forwards~: sub_transtivity H5 H2.
    forwards~: sub_transtivity H6 H4.
  - (* prod *)
    inverts~ S1; inverts~ S2; try solve_false.
    inverts H;
    apply subsub2sub in H2; apply subsub2sub in H4.
    forwards~: sub_transtivity H5 H2.
    forwards~: sub_transtivity H6 H4.
Qed.


Lemma disjoint_subsub2: forall A1 A2 B,
    subsub A1 A2 -> (disjoint A1 B <-> disjoint A2 B).
Proof.
  intros A1 A2 B H. gen B.
  induction H; intros;
    try solve [split; intros; auto].
  - (* arrow *)
    split; intros Dis;
      induction B;
      inverts* Dis;
      apply IHsubsub in H2;
      constructor*.
  - (* and *)
    split; intro Dis;
      apply disjoint_and2;
      split;
      apply disjoint_and2 in Dis;
      destruct Dis;
      try apply IHsubsub1;
      try apply IHsubsub2;
      auto.
  - (* prod *)
    split; intro Dis;
    induction B;
      inverts* Dis;
      try solve [constructor; try applys~ IHsubsub1; try applys~ IHsubsub2].
  - (* top *)
    split; intros;
      apply disjoint_eqv;
      intros T sub1 sub2;
      apply toplike_super_top;
      auto_sub.
Qed.

Lemma subsub_disjoint_l : forall x A B,
    subsub x A -> disjointSpec A B -> disjointSpec x B.
Proof.
  intros x A B H H0.
  apply disjoint_eqv.
  apply disjoint_eqv in H0.
  forwards*: disjoint_subsub2 H.
Qed.

Lemma subsub_disjoint_r : forall x A B,
    subsub x B -> disjointSpec A B -> disjointSpec A x.
Proof.
  intros x A B H H0.
  apply disjoint_symmetric.
  apply disjoint_symmetric in H0.
  forwards*: subsub_disjoint_l H.
Qed.

(* convert to arrow Type *)
Lemma arrTyp_subsub: forall A B C C',
    arrTyp C (t_arrow A B) -> subsub C' C
    -> exists A' B', arrTyp C' (t_arrow A' B') /\ sub A A' /\ subsub B' B.
Proof.
  introv Harr Hsub.
  inductions Harr.
  - inverts* Hsub.
    * exists. repeat split*. auto_sub.
    * exists. repeat split*. constructor. inverts* H.
  - inverts* Hsub.
Qed.

Lemma arrTyp_super_top: forall A B C,
    arrTyp C (t_arrow A B) -> subsub t_top C -> subsub t_top B.
Proof.
  introv Harr Hsub.
  inverts* Harr.
  - inverts Hsub.
    inverts* H.
Qed.

Lemma arrTyp_subsub_prod: forall A B C C',
    arrTyp C (t_prod A B) -> subsub C' C
    -> exists A' B', arrTyp C' (t_prod A' B') /\ subsub A' A /\ subsub B' B.
Proof.
  introv Harr Hsub.
  inductions Harr.
  - inverts* Hsub.
    inverts H.
    exists* t_top t_top.
  - inverts* Hsub.
Qed.

Lemma arrTyp_arrow_unique : forall A B1 B2 C1 C2,
    arrTyp A (t_arrow B1 B2) -> arrTyp A (t_arrow C1 C2) -> B1 = C1 /\ B2 = C2.
Proof.
  introv H1 H2.
  inductions H1; inverts~ H2.
Qed.

Lemma arrTyp_prod_unique : forall A B1 B2 C1 C2,
    arrTyp A (t_prod B1 B2) -> arrTyp A (t_prod C1 C2) -> B1 = C1 /\ B2 = C2.
Proof.
  introv H1 H2.
  inductions H1; inverts~ H2.
Qed.
