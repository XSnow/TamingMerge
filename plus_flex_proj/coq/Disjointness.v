Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Export syntax_ott.
Require Import
        rules_inf
        SubtypingInversion.


(* topLike *)
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

Lemma topLike_spl_inv : forall A B C,
    spl C A B -> topLike C -> topLike A /\ topLike B.
Proof with eauto.
  introv Hspl Htop.
  split; applys* toplike_sub Htop.
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
    inverts* H; intuition eauto.
Qed.


Lemma disjoint_andr: forall A B1 B2,
    disjoint A (t_and B1 B2) -> disjoint A B1 /\ disjoint A B2.
Proof.
  intros A B1 B2 H.
  induction A;
    inverts* H; intuition eauto.
Qed.


Lemma disjoint_rcd: forall A B l,
    disjoint (t_rcd l A) (t_rcd l B) -> disjoint A B.
Proof.
  introv H.
  inverts* H; intuition eauto.
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
      forwards: IH H6 S2; elia...
      forwards: IH H6 S2; elia...
    + inverts S2...
      forwards: IH S1 H6; elia...
      forwards: IH S1 H6; elia...
    + inverts S1; inverts S2...
      apply TL_arr.
      forwards: IH H0 H6 H10; elia...
    + inverts S1; inverts S2...
      apply TL_rcd.
      forwards: IH H0 H5 H7; elia...
  -
    inverts S1; inverts S2...
    split_unify.
    forwards (?&?): split_decrease_size H.
    applys topLike_spl H;
      eapply IH; try apply Dis; auto; elia.
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

Lemma disjoint_toplike : forall A B,
    topLike A -> disjoint A B.
Proof.
  introv H.
  applys disjoint_eqv. introv HS1 HS2.
  eauto.
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
#[export] Hint Constructors subsub : core.

Lemma subsub2sub : forall A B,
    subsub A B -> algo_sub A B.
Proof with eauto .
  intros A B H.
  induction H...
Qed.

#[export] Hint Immediate subsub2sub : core.

Lemma subsub_refl : forall A,
    subsub A A.
Proof.
  intros A.
  induction A; auto.
Qed.

#[export] Hint Resolve subsub_refl : core.

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
    apply disjoint_eqv. intros T sub1 sub2.
    applys* toplike_sub sub1.
  - split; intros.
    + forwards* (?&?): disjoint_splitl H2.
      applys disjoint_split_rev H.
      applys* IHsubsub1. applys* IHsubsub2.
    + forwards* (?&?): disjoint_splitl H2.
      applys* disjoint_split_rev.
      applys* IHsubsub1. applys* IHsubsub2.
  - split; intros Dis.
    + applys* disjoint_split_rev.
      applys~ disjoint_toplike.
      applys* IHsubsub.
    + forwards* (?&?): disjoint_splitl Dis.
      applys* IHsubsub.
  - split; intros Dis.
    + applys* disjoint_split_rev.
      applys* IHsubsub.
      applys~ disjoint_toplike.
    + forwards* (?&?): disjoint_splitl Dis.
      applys* IHsubsub.
Qed.

Lemma subsub_disjoint_l : forall x A B,
    subsub x A -> disjoint A B -> disjoint x B.
Proof.
  intros x A B H H0.
  forwards*: disjoint_subsub2 H; intuition eauto.
Qed.

Lemma subsub_disjoint_r : forall x A B,
    subsub x B -> disjoint A B -> disjoint A x.
Proof.
  intros x A B H H0.
  apply disjoint_symm.
  apply disjoint_symm in H0.
  forwards*: subsub_disjoint_l H H0; intuition eauto.
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
    forwards* (?&?): IHHsub.
  - inverts H. inverts H0.
    forwards* (?&?): IHHsub.
Qed.

Lemma subsub_rcd_inv : forall l1 l2 B D,
    subsub (t_rcd l1 B) (t_rcd l2 D) -> l1 = l2 /\ subsub B D.
Proof.
  introv Hsub.
  inductions Hsub; eauto.
  - inverts H. inverts H0.
    forwards* (?&?): IHHsub.
  - inverts H. inverts H0.
    forwards* (?&?): IHHsub.
Qed.

#[export] Hint Immediate subsub_disjoint_l subsub_disjoint_r subsub_disjoint : core.

Lemma subsub_split : forall A B A1 A2,
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
  - (* top *)
    solve_false.
Qed.

Lemma subsub_ord : forall A B,
    subsub A B -> ord B -> ord A.
Proof.
  intros A B H H0.
  induction* H; try solve [inverts* H0].
  all: solve_false.
Qed.

Lemma split_subsub : forall A B C A',
    spl A B C -> subsub A' A ->
    topLike B /\ subsub A' C
    \/ topLike C /\ subsub A' B
    \/ exists B' C', spl A' B' C' /\ subsub B' B /\ subsub C' C.
Proof.
  intros A B C A' Hspl Hss. gen B C.
  induction Hss; intros; solve_false; split_unify.
  - right. right*.
  - forwards* [(?&?) | [ (?&?) | (?&?&?&?&?)]] : IHHss H4.
    + right. left*.
    + right. right*.
  - forwards* [(?&?) | [ (?&?) | (?&?&?&?&?)]] : IHHss H3.
    + right. left*.
    + right. right*.
  - forwards* : topLike_spl_inv Hspl.
  - right. right*.
Qed.

Lemma subsub_top_inv : forall A,
    subsub A t_top -> A = t_top.
Proof.
  introv Hs. inverts* Hs; solve_false.
Qed.

Lemma subsub_toplike_1 : forall A B,
    subsub A B -> topLike A -> topLike B.
Proof.
  introv Hs Ht.
  applys toplike_sub Ht. applys~ subsub2sub.
Qed.

Lemma subsub_toplike_2 : forall A B,
    subsub A B -> topLike B -> topLike A.
Proof.
  introv Hs Ht.
  induction~ Hs.
  all: try solve [inverts* Ht].
  all: forwards*: topLike_spl H.
Qed.

Lemma subsub_trans : forall A B C,
    subsub A B -> subsub B C -> subsub A C.
Proof with (auto; solve_false; split_unify; elia; try eassumption).
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  inverts keep s1...
  - (* arrow *)
    inverts keep s2...
    + forwards: IH A2 B2 B3...
      eauto.
    + (* topL *)
      applys~ SubSub_topL H1.
      applys* IH...
    + (* topR *)
      applys~ SubSub_topR H1.
      applys* IH...
  - (* rcd *)
    inverts keep s2...
    + forwards: IH A0 B0 B...
    + (* topL *)
      applys SubSub_topL H0...
      applys* IH...
    + (* topR *)
      applys~ SubSub_topR H0...
      applys* IH...
  - (* top *)
    applys SubSub_top.
    applys~ subsub_toplike_1 s2.
  - (* spl *)
    forwards (?&?&?): subsub_split s2...
    forwards [(?&?)|[(?&?)|(?&?&?&?&?)]]: split_subsub s2; try eassumption...
    + applys SubSub_topL; try eassumption.
      applys IH B...
    + applys SubSub_topR; try eassumption.
      applys IH B...
    + applys SubSub_split H2.
      applys IH x1... applys IH x2...
  - (* topL *)
    forwards (?&?&?): subsub_split s2...
    forwards [(?&?)|[(?&?)|(?&?&?&?&?)]]: split_subsub s2; try eassumption...
    + applys~ SubSub_topL H2.
      applys IH s1...
    + applys~ SubSub_topR H2.
      applys IH s1...
    + applys SubSub_topL. eauto.
      applys* subsub_toplike_1.
      applys* IH...
  - (* topR *)
    forwards (?&?&?): subsub_split s2...
    forwards [(?&?)|[(?&?)|(?&?&?&?&?)]]: split_subsub s2; try eassumption...
    + applys~ SubSub_topL H2.
      applys IH s1...
    + applys~ SubSub_topR H2.
      applys IH s1...
    + applys SubSub_topR. eauto.
      applys* subsub_toplike_1.
      applys* IH...
Qed.

Lemma subsub_merge : forall T1 T2 A1 A2 B1 B2 C1 C2,
    spl (t_arrow T1 T2) A1 A2 -> subsub (t_arrow B1 B2) A1
    -> subsub (t_arrow C1 C2) A2
    -> subsub (t_arrow (t_and B1 C1) (t_and B2 C2)) (t_arrow T1 T2).
Proof.
  introv Hspl Hsub1 Hsub2.
  inverts Hspl.
  forwards (?&?): subsub_arr_inv Hsub1.
  forwards (?&?): subsub_arr_inv Hsub2.
  constructor*.
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


(* meg_typ : merge two types *)
Lemma meg_typ_top_r : forall A,
    meg_typ A t_top = A.
Proof.
  introv. destruct A; simpl; eauto.
Qed.

Lemma disjoint_meg: forall A B C,
    disjoint A B -> disjoint A C -> disjoint A (meg_typ B C).
Proof.
  introv dis1 dis2.
  destruct B; destruct C; simpl; eauto.
Qed.

Lemma subsub_meg_toplike: forall A B,
    topLike A -> topLike B -> subsub t_top (meg_typ A B).
Proof.
  introv TL1 TL2.
  destruct TL1; simpl; eauto.
  all: destruct TL2; simpl; eauto.
Qed.

Lemma subsub_meg: forall A B C C1 C2,
    subsub A C1 -> subsub B C2 -> spl C C1 C2
    -> subsub (meg_typ A B) C.
Proof.
  introv HA HB HC.
  destruct A; simpl; eauto.
  all: destruct B; simpl; eauto.
Qed.

(* Applicative Distributivity: convert to arrow Type *)
#[export] Hint Constructors arrTyp topLike ord spl: core.


Lemma arrTyp_arrow_form: forall A B,
    arrTyp A B -> exists B1 B2, B = t_arrow B1 B2.
Proof.
  introv Harr. inverts* Harr.
Qed.

Lemma arrTyp_split: forall A A1 A2 B,
    arrTyp A B -> spl A A1 A2 ->
    exists B1 B2 C1 C2, spl B B1 B2 /\ arrTyp A1 C1 /\ arrTyp A2 C2
                        /\ subsub C1 B1 /\ subsub C2 B2.
Proof.
  introv Harr Hspl. gen B.
  induction Hspl; intros; inverts Harr; try solve [exists; repeat split*].
Qed.

Lemma arrTyp_toplike: forall A B,
    topLike A -> arrTyp A B -> topLike B.
Proof.
  introv Htop Hat. gen B.
  induction Htop; intros.
  all: inverts~ Hat.
  - forwards: IHHtop1 H1. forwards: IHHtop2 H3.
    inverts H. inverts H0.
    repeat constructor*.
Qed.

(* used in preservation proof *)
Lemma arrTyp_subsub: forall A C' C,
    arrTyp C A -> subsub C' C
    -> exists A', arrTyp C' A' /\ subsub A' A.
Proof with try eassumption.
  introv Harr Hsub. gen A.
  induction Hsub; intros.
  - exists*.
  - inverts Harr. exists*.
  - inverts Harr.
  - forwards~ : arrTyp_toplike Harr.
    forwards~ (?&?&?) : arrTyp_arrow_form Harr. subst.
    exists* (t_arrow t_top t_top).
  - forwards~ ( T1 & T2 &?) : arrTyp_arrow_form Harr. subst.
    forwards* (?&?&?&?&?&?&?&?&?): arrTyp_split Harr.
    forwards (?&?&?): IHHsub1...
    forwards (?&?&?): IHHsub2...
    forwards (?&?&?) : arrTyp_arrow_form A1...
    forwards (?&?&?) : arrTyp_arrow_form A2... subst.
    exists. split*. applys subsub_merge H0.
    all: applys* subsub_trans.
  - forwards~ ( T1 & T2 &?) : arrTyp_arrow_form Harr. subst.
    forwards* (?&?&?&?&?&?&?&?&?): arrTyp_split Harr.
    forwards (?&?&?): IHHsub...
    exists. split*.
    applys* subsub_trans. applys~ SubSub_topL H1.
    applys* subsub_toplike_1. applys* arrTyp_toplike.
  - forwards~ ( T1 & T2 &?) : arrTyp_arrow_form Harr. subst.
    forwards* (?&?&?&?&?&?&?&?&?): arrTyp_split Harr.
    forwards (?&?&?): IHHsub...
    exists. split*.
    applys* subsub_trans. applys~ SubSub_topR H1.
    applys* subsub_toplike_1. applys* arrTyp_toplike.
Qed.


Lemma rcdTyp_toplike: forall l A B,
    topLike A -> rcdTyp l A B -> topLike B.
Proof.
  introv Htop Hat. gen B.
  induction Htop; intros.
  all: inverts~ Hat.
  destruct A'; destruct B'; simpl; eauto.
Qed.

Lemma rcdTyp_split: forall l A A1 A2 B,
    rcdTyp l A B -> spl A A1 A2 ->
    exists C1 C2, rcdTyp l A1 C1 /\ rcdTyp l A2 C2 /\
    (C1 = t_top /\ B = C2 \/ C2 = t_top /\ B = C1 \/ spl B C1 C2).
Proof.
  introv Harr Hspl. gen B.
  inverts Hspl; intros; inverts* Harr.
  - exists. repeat split*.
    destruct A'; destruct B'; simpl; eauto.
Qed.

Lemma rcdTyp_subsub: forall l A1 C C',
    rcdTyp l C A1 -> subsub C' C
    -> exists A2, rcdTyp l C' A2 /\ subsub A2 A1.
Proof.
  introv Hrcd Hsub. gen l A1.
  induction Hsub; intros;
    try solve [inverts* Hrcd].
  - exists t_top; inverts* Hrcd.
    all: inverts* H.
    forwards~ TL1: rcdTyp_toplike H0.
    forwards~ TL2 : rcdTyp_toplike H1.
    split*. applys~ subsub_meg_toplike.
  - forwards (?&?&?&?&[(?&?)|[(?&?)|?]]): rcdTyp_split Hrcd H; subst.
    + forwards* (T1 &?&?): IHHsub1.
      forwards* (T2 &?&?): IHHsub2.
      exists (meg_typ T1 T2). split*.
      forwards: subsub_top_inv H3. subst*.
    + forwards* (T1 &?&?): IHHsub1.
      forwards* (T2 &?&?): IHHsub2.
      exists (meg_typ T1 T2). split*.
      forwards: subsub_top_inv H5. subst*.
      rewrite* meg_typ_top_r.
    + forwards* (T1 &?&?): IHHsub1.
      forwards* (T2 &?&?): IHHsub2.
      exists (meg_typ T1 T2). split*.
      applys* subsub_meg.
  - forwards (?&?&?&?&[(?&?)|[(?&?)|?]]): rcdTyp_split Hrcd H; subst.
    all: forwards*: rcdTyp_toplike H0.
    all: forwards* (?&?&?): IHHsub.
    + forwards: subsub_top_inv H5; subst.
      exists. split*.
  - forwards (?&?&?&?&[(?&?)|[(?&?)|?]]): rcdTyp_split Hrcd H; subst.
    all: forwards*: rcdTyp_toplike H0.
    all: forwards* (?&?&?): IHHsub.
    + forwards: subsub_top_inv H5; subst.
      exists. split*.
Qed.

(* used in preservation proof *)
Lemma arrTyp_unique: forall A B C,
    arrTyp A B -> arrTyp A C -> B = C.
Proof.
  introv H1 H2. gen C.
  inductions H1; intros; inverts~ H2.
  forwards~ : IHarrTyp1 H1.
  forwards~ : IHarrTyp2 H4.
  inverts H. inverts H0. congruence.
Qed.

Lemma rcdTyp_unique: forall l A B C,
    rcdTyp l A B -> rcdTyp l A C -> B = C.
Proof.
  introv HR1 HR2. gen C.
  induction HR1; intros; inverts~ HR2; solve_false.
  forwards* : IHHR1_1. forwards* : IHHR1_2. subst*.
Qed.

Lemma arrTyp_disjoint: forall A B A1 A2 B1 B2,
    arrTyp A (t_arrow A1 A2) -> arrTyp B (t_arrow B1 B2)
    -> disjoint A B -> disjoint A2 B2.
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

Lemma rcdTyp_disjoint: forall l A A' B B',
    rcdTyp l A A' -> rcdTyp l B B' -> disjoint A B -> disjoint A' B'.
Proof.
  introv sub1 sub2 dis1. gen B B'.
  induction sub1; intros; eauto.
  - induction* sub2.
    forwards* (?&?): disjoint_andr dis1.
    applys* disjoint_meg.
  - forwards* (?&?): disjoint_andl dis1.
    forwards* : IHsub1_1 H.
    forwards* : IHsub1_2 H0.
    applys disjoint_symm.
    applys disjoint_meg; applys* disjoint_symm.
Qed.
