Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Export syntax_ott.
Require Import
        rules_inf
        SubtypingInversion.


(* topLike *)
Theorem topLike_eqv: forall A,
    topLike A <-> topLikeR A.
Proof with eauto.
  split; intros H.
  - apply topLike_super_top in H.
    inductions H...
    induction~ H0; inverts H...
  - apply topLike_super_top.
    inductions H; auto; eauto;
      apply topLike_super_top in IHtopLikeR;
      apply~ S_top.
Qed.


Lemma topLike_spl : forall A B C,
    spl C A B -> topLike A -> topLike B -> topLike C.
Proof with eauto.
  intros A B C H H0 H1.
  apply topLike_super_top.
  inductions H...
Qed.


Lemma toplike_sub: forall A B,
    topLike A -> algo_sub A B -> topLike B.
Proof.
  intros A B H H0.
  apply topLike_super_top in H.
  apply topLike_super_top.
  auto_sub.
Qed.


Lemma toplike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof with jauto.
  induction A...
  - right. intro H. inverts H.
  - destruct IHA2...
  - destruct IHA1...
    + destruct IHA2...
  - destruct IHA...
    + right. intro H'. inverts~ H'.
Qed.

(* disjoint *)
Definition disjointSpec A B :=
  forall C, algo_sub A C -> algo_sub B C -> topLike C.


#[export] Hint Constructors disjoint : core.

Lemma disjoint_andl: forall A1 A2 B,
    disjoint (t_and A1 A2) B -> disjoint A1 B /\ disjoint A2 B.
Proof.
  intros A1 A2 B H.
  induction B;
    inverts* H.
Qed.


Lemma disjoint_andr: forall A B1 B2,
    disjoint A (t_and B1 B2) -> disjoint A B1 /\ disjoint A B2.
Proof.
  intros A B1 B2 H.
  induction A;
    inverts* H.
Qed.


Lemma disjoint_rcd: forall A B l,
    disjoint (t_rcd l A) (t_rcd l B) -> disjoint A B.
Proof.
  introv H.
  inverts* H.
Qed.

#[export] Hint Immediate disjoint_rcd : core.


Lemma disjoint_completeness: forall A B,
    disjoint A B -> disjointSpec A B.
Proof with (solve_false; auto).
  intros A B Dis C S1 S2.
  indTypSize (size_typ A + size_typ B + size_typ C).

  forwards [?|(?&?&?)]: ord_or_split C.
  - inverts Dis; try solve [apply~ topLike_super_top];
      try solve [inverts S1; inverts S2; solve_false; auto]...
    + inverts S1...
      forwards: IH H6 S2; eomg...
      forwards: IH H6 S2; eomg...
    + inverts S2...
      forwards: IH S1 H6; eomg...
      forwards: IH S1 H6; eomg...
    + inverts S1; inverts S2...
      apply TL_arr.
      forwards: IH H0 H6 H10; eomg...
    + inverts S1; inverts S2...
      apply TL_rcd.
      forwards: IH H0 H5 H7; eomg...
  -
    inverts S1; inverts S2...
    split_unify.
    forwards (?&?): split_decrease_size H.
    applys topLike_spl H;
      eapply IH; try apply Dis; auto; eomg.
Qed.


Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - gen B.
    induction A;
      introv H;
      induction B; auto .
    + (* int int *)
      assert (~topLike t_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards: (H t_int); auto. tryfalse.
    + (* arr arr *)
      constructor.
      clear IHA1 IHB1.
      apply IHA2. intros.
      assert (TL: topLike (t_arrow (t_and A1 B1) C)). {
        apply H;
          subst; auto .
      }
      inverts* TL.
    + (* rcd rcd *)
      destruct (l == l0); auto. subst.
      apply D_rcdEq. apply IHA. introv s1 s2.
      assert (TL: topLike (t_rcd l0 C) ). {
        apply~ H.
      }
      inverts~ TL.
  - apply disjoint_completeness.
Qed.


Lemma disjoint_domain_type: forall A B C B',
    disjoint (t_arrow B C) A -> disjoint (t_arrow B' C) A.
Proof.
  intros A B C B' H.
  induction* A;
    invert* H.
Qed.


Lemma disjoint_splitl: forall A B C D,
    spl D B C -> disjoint D A -> disjoint B A /\ disjoint C A.
Proof with auto .
  intros A B C D HS HD.
  apply disjoint_eqv in HD. unfolds in HD.
  split; apply disjoint_eqv; unfolds; intros T S1 S2.
  - destruct HS...
    + apply~ HD.
      assert (algo_sub (t_arrow A0 B) (t_arrow A0 C)). {
        apply~ sub_fun.
        eauto.
      }
      auto_sub.
    + apply~ HD.
      applys trans S1. apply~ sub_rcd. auto_sub.
  - destruct HS...
    + apply~ HD.
      assert (algo_sub (t_arrow A0 B) (t_arrow A0 D)). {
        apply~ sub_fun.
        eauto.
      }
      auto_sub.
    + apply~ HD. applys trans S1. apply~ sub_rcd. auto_sub.
Qed.


Lemma disjoint_symm: forall A B,
    disjoint A B -> disjoint B A.
Proof.
  intros A B H.
  apply disjoint_eqv. apply disjoint_eqv in H.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  apply~ H.
Qed.

#[export] Hint Immediate disjoint_symm : core.


Lemma disjoint_splitr: forall A B C D,
    spl D B C -> disjoint A D -> disjoint A B /\ disjoint A C.
Proof.
  intros A B C D HS HD.
  apply disjoint_symm in HD.
  forwards(?&?): disjoint_splitl HS HD.
  split; apply disjoint_symm; auto.
Qed.

Lemma disjoint_sub: forall A A' B,
    disjoint A B -> algo_sub A A' -> disjoint A' B.
Proof.
  intros A A' B H H0.
  apply disjoint_eqv in H.
  apply disjoint_eqv.
  unfolds. intros.
  assert (algo_sub A C) by auto_sub.
  apply~ H.
Qed.

Lemma disjoint_split_rev: forall A B C D,
    spl D B C -> disjoint B A -> disjoint C A -> disjoint D A.
Proof.
  intros A B C D Hspl dis1 dis2.
  apply split_sub in Hspl.
  lets*: D_andL dis1 dis2.
  forwards*: disjoint_sub H Hspl.
Qed.


Lemma disjoint_dec: forall A B,
    disjoint A B \/ ~ disjoint A B.
Proof with auto.
  intros A B. gen B.
  induction A; intros; auto.
  - induction B; auto;
      try solve [ right; intros H; inverts* H ].
    destruct IHB1.
    + destruct IHB2...
      right; intros H'. inverts* H'.
    + right; intros H'. inverts* H'.
  - clear IHA1.
    induction B...
    + destruct (IHA2 B2)...
      right; intros H'; inverts* H'.
    + destruct IHB1...
      destruct IHB2...
      * right; intros H'. inverts* H'.
      * right; intros H'. inverts* H'.
  - destruct (IHA1 B)...
    destruct (IHA2 B)...
    * right; intros H'.
      lets* (?&?): disjoint_andl H'.
    * right; intros H'.
      lets* (?&?): disjoint_andl H'.
  - (* rcd *)
    induction B...
    + destruct IHB1...
      destruct IHB2...
      * right; intros H'. inverts* H'.
      * right; intros H'. inverts* H'.
    + destruct (l==l0); eauto; subst.
      destruct (IHA B)...
      * right; intros H'.
        inverts~ H'.
Qed.

(* subsub *)
Lemma subsub2sub : forall A B,
    subsub A B -> algo_sub A B.
Proof with eauto .
  intros A B H.
  induction H...
  - apply split_sub in H. destruct H.
    apply split_sub in H0. destruct H0.
    assert (algo_sub (t_and A1 A2) (t_and B1 B2))...
    applys trans...
Qed.

#[export] Hint Immediate subsub2sub : core.
#[export] Hint Constructors subsub : core.

Lemma subsub_refl : forall A,
    subsub A A.
Proof.
  intros A.
  induction A; auto.
Qed.

#[export] Hint Resolve subsub_refl : core.

Lemma split_subsub : forall A B C A',
    spl A B C -> subsub A A' ->
    exists B' C', spl A' B' C' /\ subsub B B' /\ subsub C C'.
Proof.
  intros A B C A' Hspl Hss. gen B C.
  induction Hss; intros; solve_false.
  - split_unify. eauto.
  - split_unify. forwards* (?&?&?&?&?): IHHss H4.
    exists. repeat split*.
  - split_unify. forwards* (?&?&?&?&?): IHHss H3.
    exists. repeat split*.
  - split_unify. eauto.
Qed.


Lemma disjoint_subsub2: forall A1 A2 B,
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
  - split; intros Dis;
      induction~ B0;
      inverts* Dis;
      apply IHsubsub in H1;
      constructor*.
  - split*; intros.
    apply disjoint_eqv.
    intros T sub1 sub2.
    apply topLike_super_top in H0.
    apply topLike_super_top.
    auto_sub.
  - split; intros.
    + lets* subA1: spl_sub_l H. lets* subA2: spl_sub_r H.
      lets* disA1: disjoint_sub H3 subA1.
      lets* disA2: disjoint_sub H3 subA2.
      apply IHsubsub1 in disA1.
      apply IHsubsub2 in disA2.
      lets* (?&subB): split_sub H0.
      eapply disjoint_sub; try apply subB.
      eauto.
    + lets* (dis1 & dis2): disjoint_splitl H0 H3.
      apply IHsubsub1 in dis1.
      apply IHsubsub2 in dis2.
      lets* (?&subA): split_sub H.
      eapply disjoint_sub; try apply subA.
      eauto.
Qed.

Lemma subsub_disjoint_l : forall x A B,
    subsub x A -> disjoint A B -> disjoint x B.
Proof.
  intros x A B H H0.
  forwards*: disjoint_subsub2 H.
Qed.

Lemma subsub_disjoint_r : forall x A B,
    subsub x B -> disjoint A B -> disjoint A x.
Proof.
  intros x A B H H0.
  apply disjoint_symm.
  apply disjoint_symm in H0.
  forwards*: subsub_disjoint_l H H0.
Qed.

Lemma subsub_disjoint : forall x1 x2 A B,
    subsub x1 A -> subsub x2 B -> disjoint A B -> disjoint x1 x2.
Proof.
  intros x1 x2 A B H H0 H1.
  applys~ subsub_disjoint_l H.
  applys~ subsub_disjoint_r H0.
Qed.

Lemma subsub_arr_inv : forall A B C D,
    subsub (t_arrow A B) (t_arrow C D) -> algo_sub C A /\ subsub B D.
Proof.
  introv Hsub.
  inductions Hsub; eauto.
  - inverts H. inverts H0.
    forwards* (?&?): IHHsub1.
    forwards* (?&?): IHHsub2.
Qed.

Lemma subsub_rcd_inv : forall l1 l2 B D,
    subsub (t_rcd l1 B) (t_rcd l2 D) -> l1 = l2 /\ subsub B D.
Proof.
  introv Hsub.
  inductions Hsub; eauto.
  - inverts H. inverts H0.
    forwards* (?&?): IHHsub1.
    forwards* (?&?): IHHsub2.
Qed.

Lemma subsub_spl_inv : forall A A1 A2 B B1 B2,
    subsub A B -> spl A A1 A2 -> spl B B1 B2 -> subsub A1 B1 /\ subsub A2 B2.
Proof.
  introv Hs Hspl1 Hspl2. gen A1 A2 B1 B2.
  inductions Hs; intros; split_unify; try solve_false.
  - forwards* (?&?): IHHs H5.
  - forwards* (?&?): IHHs H4.
Qed.

#[export] Hint Immediate subsub_disjoint_l subsub_disjoint_r subsub_disjoint : core.

Lemma subsub_split : forall A A1 A2 B,
    subsub A B -> spl A A1 A2 -> exists B1 B2, spl B B1 B2.
Proof.
  introv Hs Hspl. gen A1 A2.
  induction* Hs; intros.
  - (* arr *)
    inverts Hspl.
    forwards* (?&?&?): IHHs.
  - (* rcd *)
    inverts Hspl.
    forwards* (?&?&?): IHHs.
  - inverts Hspl.
Qed.

Lemma subsub_split2 : forall A B B1 B2,
    subsub A B -> spl B B1 B2 -> exists A1 A2, spl A A1 A2.
Proof.
  introv Hs Hspl. gen B1 B2.
  induction* Hs; intros.
  - (* arr *)
    inverts Hspl.
    forwards* (?&?&?): IHHs.
  - (* rcd *)
    inverts Hspl.
    forwards* (?&?&?): IHHs.
  - (* top *)
    solve_false.
Qed.

Lemma subsub_ord : forall A B,
   subsub A B ->  ord A -> ord B.
Proof.
  intros A B H H0.
  induction* H; try solve [inverts* H0].
  solve_false.
Qed.

Lemma subsub_trans : forall A B C,
    subsub A B -> subsub B C -> subsub A C.
Proof with (auto; solve_false).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts keep s2...
    + (* arrow *)
      inverts keep s1; simpl in SizeInd...
      * assert (subsub A3 B2). {
          applys IH; try eassumption.
          eomg.
        }
        eauto.
      * (* top *)
        forwards: subsub_ord s2; try eassumption; eauto.
        apply subsub2sub in s2.
        apply toplike_sub in s2...
      * (* spl *)
        forwards (?&?&?): subsub_split s2; try eassumption.
        forwards (?&?): subsub_spl_inv s2; try eassumption.
        lets (?&?): split_decrease_size H1.
        lets (?&?): split_decrease_size H2.
        lets (?&?): split_decrease_size H5.
        applys SubSub_split; try eassumption; applys IH; try eassumption; eomg.
    + (* rcd *)
      inverts s1; simpl in SizeInd...
      * assert (subsub A1 B0). {
          applys IH; try eassumption.
          eomg.
        }
        eauto.
      * (* top *)
        forwards: subsub_ord s2; try eassumption; eauto.
        apply subsub2sub in s2.
        apply toplike_sub in s2...
      * (* spl *)
        forwards (?&?&?): subsub_split s2; try eassumption.
        forwards (?&?): subsub_spl_inv s2; try eassumption.
        lets (?&?): split_decrease_size H0.
        lets (?&?): split_decrease_size H1.
        lets (?&?): split_decrease_size H4.
        applys SubSub_split; try eassumption; applys IH; try eassumption; eomg.
    + (* top *)
      inverts s1...
    + (* spl *)
      forwards (?&?&?): subsub_split2 s1; try eassumption.
        forwards (?&?): subsub_spl_inv s1; try eassumption.
        lets (?&?): split_decrease_size H3.
        lets (?&?): split_decrease_size H0.
        lets (?&?): split_decrease_size H.
        assert (subsub x B1). {
          applys IH; try eassumption.
          eomg.
        }
        assert (subsub x0 B2). {
          applys IH; try eassumption.
          eomg.
        }
        applys~ SubSub_split H12 H13.
Qed.

Lemma sub_andl : forall A B,
    algo_sub (t_and A B) A.
Proof.
  intros. auto_sub.
Qed.

Lemma sub_andr : forall A B,
    algo_sub (t_and A B) B.
Proof.
  intros. auto_sub.
Qed.

#[export] Hint Resolve sub_andl sub_andr : core.

(* Applicative Distributivity: convert to arrow Type *)
#[export] Hint Constructors arrTyp topLike ord spl: core.

Lemma arrTyp_split: forall A A1 A2 B,
    arrTyp A B -> spl A A1 A2 ->
    exists C1 C2, arrTyp A1 C1 /\ arrTyp A2 C2  /\ subsub (t_and C1 C2) B. (* spl B B1 B2 /\ subsub C1 B1 /\ subsub C2 B2. *)
Proof.
  introv Harr Hspl. gen B.
  induction Hspl; intros; inverts Harr; try solve [exists; repeat split*].
Qed.

(* A1 -> A2 & B1 -> B2 <<: C1 -> C2 & D1 -> D2
   A1&B2 -> B1&B2 <<: A1 -> B1&B2 *)
(* used in preservation proof *)
Lemma arrTyp_arr_subsub: forall A1 A2 C C',
    arrTyp C (t_arrow A1 A2) -> subsub C' C
    -> exists A1' A2', arrTyp C' (t_arrow A1' A2') /\ subsub (t_arrow A1' A2') (t_arrow A1 A2).
Proof.
  introv Harr Hsub. gen A1 A2.
  induction Hsub; intros.
  - exists*.
  - inverts Harr. exists. repeat split*.
  - inverts Harr.
  - inverts Harr; try solve_false.
    + inverts H0. inverts H. exists; split. apply AT_topArr. jauto.
    + exists; split. apply AT_topArr. jauto.
  - inverts H0.
    + inverts Harr.
      forwards* ( A1' &?&?&?): IHHsub1 H3.
      forwards* ( A2' &?&?&?): IHHsub2 H5.
      inverts H; try solve [inverts H0].
      * exists (t_and A1' A2') (t_and x x0).
        split*.
        forwards* (?&?): subsub_arr_inv H1.
        forwards* (?&?): subsub_arr_inv H4.
      * exists. split*. inverts H0. inverts H2.
        forwards* (?&?): subsub_arr_inv H1.
        forwards* (?&?): subsub_arr_inv H4.
    + inverts Harr.
      forwards* ( A1' &?&?&?): IHHsub1.
      forwards* ( A2' &?&?&?): IHHsub2.
      inverts H; try solve [inverts H0].
      * exists (t_and A1' A2') (t_and x x0).
        split*.
        forwards* (?&?): subsub_arr_inv H2.
        forwards* (?&?): subsub_arr_inv H4.
      * exists. split*.
    + inverts Harr.
Qed.

Lemma arrTyp_rcd_subsub: forall l A2 C C',
    arrTyp C (t_rcd l A2) -> subsub C' C
    -> exists A2', arrTyp C' (t_rcd l A2') /\ subsub (t_rcd l A2') (t_rcd l A2).
Proof.
  introv Harr Hsub. gen l A2.
  induction Hsub; intros.
  - exists*.
  - inverts Harr.
  - inverts Harr. exists. repeat split*.
  - inverts Harr; try solve_false.
    + inverts H0. inverts H. exists; split. apply AT_topRcd. jauto.
    + exists; split. apply AT_topRcd. jauto.
  - inverts H0.
    + inverts Harr.
      forwards* ( A1' &?&?): IHHsub1.
      forwards* ( A2' &?&?): IHHsub2.
      inverts keep H; try solve [inverts H0].
      * exists* (t_and A1' A2').
      * inverts H0. inverts H2.
        exists B. split*.
    + inverts Harr.
    + inverts Harr.
      forwards* ( A1' &?&?): IHHsub1.
      forwards* ( A2' &?&?): IHHsub2.
      inverts H; try solve [inverts H0].
      * exists (t_and A1' A2').
        split*.
      * inverts H0. inverts H3.
        exists B. split*.
Qed.

(* used in preservation proof *)
Lemma arrTyp_arrow_unique: forall A B1 B2 C1 C2,
    arrTyp A (t_arrow B1 B2) -> arrTyp A (t_arrow C1 C2) -> B1 = C1 /\ B2 = C2.
Proof.
  introv H1 H2. gen C1 C2.
  inductions H1; intros; inverts~ H2.
  forwards~ (?&?): IHarrTyp1 H3.
  forwards~ (?&?): IHarrTyp2 H5.
  split; congruence.
Qed.

Lemma arrTyp_rcd_unique: forall A l B2 C2,
    arrTyp A (t_rcd l B2) -> arrTyp A (t_rcd l C2) -> B2 = C2.
Proof.
  introv H1. gen C2.
  inductions H1; intros; inverts~ H.
  forwards* : IHarrTyp1. forwards* : IHarrTyp2.
  congruence.
Qed.

Lemma arrTyp_arr_disjoint: forall A B A1 A2 B1 B2,
    arrTyp A (t_arrow A1 A2) -> arrTyp B (t_arrow B1 B2) ->  disjoint A B -> disjoint A2 B2.
Proof.
  introv sub1 sub2 dis1. gen B B1 B2.
  inductions sub1; intros.
  - inductions sub2; eauto.
    + inverts~ dis1.
    + apply disjoint_andr in dis1.
      destruct dis1. eauto.
  - eauto.
  - lets* (?&?): disjoint_andl dis1.
Qed.

Lemma arrTyp_rcd_disjoint: forall A B l A' B',
    arrTyp A (t_rcd l A') -> arrTyp B (t_rcd l B') ->  disjoint A B -> disjoint A' B'.
Proof.
  introv sub1 sub2 dis1. gen B B'.
  inductions sub1; intros.
  - inductions sub2; eauto.
    + apply disjoint_andr in dis1.
      destruct dis1. eauto.
  - eauto.
  - lets* (?&?): disjoint_andl dis1.
Qed.
