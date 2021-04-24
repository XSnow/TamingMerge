Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import syntax_ott
               rules_inf.

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

#[export]
Hint Resolve ord_and_inv toplike_int_inv toplike_arrow_inv : falseHd.


(* topLike *)
Lemma toplike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof.
  intro A.
  split.
  - intro H.
    induction~ H.
  - intro H.
    induction~ A;
      try solve [inverts* H].
Qed.

Lemma toplike_sub: forall A B,
    topLike A -> sub A B -> topLike B.
Proof.
  introv TL S.
  induction S; inverts* TL.
Qed.

Lemma toplike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof.
  intros.
  induction~ A;
    try solve [ right; intros HF; inverts~ HF ].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [ right; intros HF; inverts~ HF ].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [ right; intros HF; inverts~ HF ].
Qed.

#[export]
Hint Resolve toplike_super_top : core.

(* subtyping *)
Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> topLike B2 \/ (sub B1 A1 /\ sub A2 B2).
Proof.
  intros.
  inverts* H.
  - inverts* H0.
Qed.

Lemma sub_inversion_arrow_r : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub A2 B2.
Proof.
  intros.
  forwards* [?|?]: sub_inversion_arrow H.
Qed.

Lemma sub_inversion_arrow_l : forall A1 A2 B1 B2,
    ~ topLike B2 -> sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub B1 A1.
Proof.
  intros.
  forwards* [?|?]: sub_inversion_arrow H0.
Qed.

Lemma sub_inversion_and_l : forall A1 A2 B,
    sub (t_and A1 A2) B -> sub A1 B \/ sub A2 B \/ exists B1 B2, B = t_and B1 B2.
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_reflexivity : forall A,
    sub A A.
Proof.
  intros A.
  induction* A.
Qed.

#[export]
Hint Resolve sub_reflexivity : core.

Lemma and_inversion : forall A B C,
    sub A (t_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  inductions H; eauto.
  - inverts* H.
  - lets*: IHsub B C.
  - lets*: IHsub B C.
Qed.

Lemma sub_transtivity : forall B A C,
      sub A B -> sub B C -> sub A C.
Proof with eauto.
  introv S1 S2. gen A C.
  induction B; intros;
    try solve [inductions S2; eauto].
  - inductions S2...
    clear IHS2_1 IHS2_2.
    inductions S1...
    applys S_top. applys toplike_sub H...
  - forwards* (?&?): and_inversion S1.
    inductions S2...
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
        (applys~ sub_transtivity H)
      | [ H: topLike ?A |- sub _ ?A ] =>
        (applys~ S_top)
      | [ H: topLike ?A |- sub _ (t_arrow _ ?A) ] =>
        (apply TL_arr in H; apply S_top; auto)
      | [ H: sub (t_arrow _ _) (t_arrow _ _) |- sub _ _ ] => (apply sub_inversion_arrow in H; destruct H; auto_sub)
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
    | |- _ => try constructor*
      end.


(* disjoint *)
Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B. unfold disjointSpec.
  split.
  - gen B.
    induction A; intros; induction B;
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
        apply H; subst*.
      }
      subst.
      inverts* TL.
  - intros H C S1 S2. gen C.
    induction* H; intros; induction* C;
      try solve [applys* toplike_super_top];
      (* when A is an intersection type *)
      try (forwards* [?|[?|(?&?&HF)]]: sub_inversion_and_l S1; inverts HF);
      (* when B is an intersection type *)
      try (forwards* [?|[?|(?&?&HF)]]: sub_inversion_and_l S2; inverts HF);
      (* when C is an intersection type *)
    try solve [ applys TL_and;
                [forwards*: IHC1 | forwards*: IHC2];
                auto_sub ];
    (* when S1/S2 is impossible *)
    try solve [inverts~ S1];
    try solve [inverts~ S2].
    (* all are arrow types *)
    forwards* : sub_inversion_arrow_r S1.
    forwards* : sub_inversion_arrow_r S2.
Qed.


Lemma disjoint_and_inv: forall A B C,
    disjoint (t_and B C) A <-> disjoint B A /\ disjoint C A.
Proof.
  split; intro H.
  - split; induction A; invert* H.
  - destruct H; induction* A.
Qed.


Lemma disjointSpec_and_inv: forall A B C,
    disjointSpec (t_and B C) A <-> disjointSpec B A /\ disjointSpec C A.
Proof.
  split;
  intro H.
  - apply disjoint_eqv in H.
    apply disjoint_and_inv in H.
    split; apply disjoint_eqv; jauto.
  - destruct H.
    apply disjoint_eqv in H.
    apply disjoint_eqv in H0.
    apply disjoint_eqv.
    applys~ disjoint_and_inv.
Qed.

Lemma disjointSpec_symmetric: forall A B,
    disjointSpec A B -> disjointSpec B A.
Proof.
  intros A B H.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  applys~ H.
Qed.

Lemma disjoint_symmetric: forall A B,
    disjoint A B -> disjoint B A.
Proof.
  intros A B H.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  applys~ disjointSpec_symmetric.
Qed.


Lemma disjointSpec_domain_type: forall A B C B',
    disjointSpec (t_arrow B C) A -> disjointSpec (t_arrow B' C) A.
Proof.
  intros A B C B' H.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  induction* A;
    invert* H.
Qed.


(* Runtime Subtyping *)
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
      apply subsub2sub in H4.
      lets*: toplike_sub H.
  - (* and *)
    inverts~ S1; inverts~ S2; try solve_false.
    apply subsub2sub in H2. apply subsub2sub in H4.
    lets*: toplike_sub H.
Qed.


Lemma disjoint_subsub: forall A1 A2 B,
    subsub A1 A2 -> (disjoint A1 B <-> disjoint A2 B).
Proof.
  intros A1 A2 B H. gen B.
  induction H; intros;
    try solve [split; intros; auto].
  - split; intros Dis;
      induction B;
      inverts* Dis;
      apply IHsubsub in H2;
      constructor*.
  - split; intro Dis;
      apply disjoint_and_inv;
      split;
      apply disjoint_and_inv in Dis;
      destruct Dis;
      try apply IHsubsub1;
      try apply IHsubsub2;
      auto.
  - split; intros;
      apply disjoint_eqv;
      intros T sub1 sub2.
    applys~ toplike_sub H.
    applys~ toplike_super_top.
Qed.

Lemma subsub_disjointSpec_l : forall x A B,
    subsub x A -> disjointSpec A B -> disjointSpec x B.
Proof.
  intros x A B H H0.
  apply disjoint_eqv.
  apply disjoint_eqv in H0.
  forwards*: disjoint_subsub H.
Qed.

Lemma subsub_disjointSpec_r : forall x A B,
    subsub x B -> disjointSpec A B -> disjointSpec A x.
Proof.
  intros x A B H H0.
  apply disjointSpec_symmetric.
  apply disjointSpec_symmetric in H0.
  forwards*: subsub_disjointSpec_l H.
Qed.


(* Applicative Distributivity: convert a type to an arrow Type *)
Lemma arrTyp_subsub: forall A B C C',
    arrTyp C (t_arrow A B) -> subsub C' C
    -> exists A' B', arrTyp C' (t_arrow A' B') /\ sub A A' /\ subsub B' B.
Proof.
  introv Harr Hsub.
  inductions Harr.
  - inverts* Hsub.
    * exists. repeat split*. inverts* H.
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

Lemma arrTyp_unique: forall A B C,
    arrTyp A B -> arrTyp A C -> B = C.
Proof.
  intros A B C H1 H2.
  induction H1; inverts~ H2.
Qed.
