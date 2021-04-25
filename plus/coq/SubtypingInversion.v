Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Export syntax_ott.
Require Import rules_inf.
Require Import Lia.


(* R: proper types *)
Inductive R : typ -> Prop :=
| R_int : R t_int
| R_top : R t_top
| R_ordFun : forall A B, ord B -> R A -> R B -> R (t_arrow A B)
| R_ordRcd : forall l A, ord A -> R A -> R (t_rcd l A)
| R_spl : forall B C A, spl A B C -> R B -> R C -> R A.

#[local]
Hint Constructors R : core.


Lemma rfun : forall B, R B -> forall A, R A -> R (t_arrow A B).
Proof.
  intros B RB.
  induction RB; intros; eauto.
Qed.

Lemma rrcd : forall A, R A-> forall l, R (t_rcd l A).
Proof.
  intros A RA.
  induction RA; intros; eauto.
Qed.

Lemma types_are_proper : forall A, R A.
Proof.
  introv. induction* A.
  - apply~ rfun.
  - apply~ rrcd.
Qed.

Ltac proper_ind A := assert (r: R A) by apply (types_are_proper A); induction r.


(* split *)
Lemma split_ord_false : forall T T1 T2,
    spl T T1 T2 -> ord T -> False.
Proof.
  introv s o. gen T1 T2.
  induction o; intros; inverts* s.
Qed.

#[export]
Hint Resolve split_ord_false : falseHd.


Ltac solve_false := try intro; try solve [false; eauto with falseHd].


Lemma ord_or_split: forall A,
    ord A \/ exists B C, spl A B C.
Proof.
  intros A. induction* A.
  lets* [?|(?&?&?)]: IHA2.
  -
    destruct~ IHA as [?|(?&?&?)].
    right*.
Qed.
(*
Ltac destructT A := lets [?|(?&?&?)]: (ord_or_split A).
*)

Lemma split_unique : forall T A1 A2 B1 B2,
    spl T A1 B1 -> spl T A2 B2 -> A1 = A2 /\ B1 = B2.
Proof.
  introv s1 s2. gen A2 B2.
  induction s1; intros;
    inverts* s2;
    forwards* (eq1&eq2): IHs1; split; congruence.
Qed.

Ltac split_unify :=
  repeat match goal with
  | [ H1: spl ?A _ _ , H2: spl ?A _ _ |- _ ] =>
           (progress forwards (?&?): split_unique H1 H2;
            subst; clear H2)
  | [ H: spl (t_and _ _) _ _ |- _ ] => inverts H
  | [ H: spl (t_arrow _ _) _ _ |- _ ] => inverts H
  | [ H: spl (t_rcd _ _) _ _ |- _ ] => inverts H
         end;
  auto.


(* topLike *)
Lemma topLike_arrow_inv : forall A B,
    topLike (t_arrow A B) -> topLike B.
Proof.
  introv H. inverts~ H.
Qed.

Lemma topLike_and_l_inv : forall A B,
    topLike (t_and A B) -> topLike A.
Proof.
  introv H. inverts~ H.
Qed.

Lemma topLike_and_r_inv : forall A B,
    topLike (t_and A B) -> topLike B.
Proof.
  introv H. inverts~ H.
Qed.

#[export]
Hint Immediate topLike_arrow_inv topLike_and_l_inv topLike_and_r_inv: core.


Lemma topLike_spl_combine: forall A B C,
    spl C A B -> topLike A -> topLike B -> topLike C.
Proof.
  introv s tl1 tl2. induction* s.
  inverts tl1. inverts tl2. auto.
Qed.

Lemma topLike_split_l_inv: forall A B C,
    topLike C -> spl C A B -> topLike A.
Proof.
  introv tl s. induction* s.
  inverts* tl.
Qed.

Lemma topLike_split_r_inv: forall A B C,
    topLike C -> spl C A B -> topLike B.
Proof.
  introv tl s. induction* s.
  inverts* tl.
Qed.

#[export]
Hint Immediate topLike_spl_combine topLike_split_l_inv topLike_split_r_inv : core.

(* topLike specification eqv *)
Lemma topLike_super_top: forall A,
    topLike A <-> algo_sub t_top A.
Proof with eauto.
  split; intros H.
  - proper_ind A...
  - inductions H... iauto.
Qed.

Lemma toplike_sub : forall A B,
    topLike A -> algo_sub A B -> topLike B.
Proof.
  introv TL S.
  induction S; inverts* TL;
    applys* topLike_spl_combine.
Qed.

#[export]
 Hint Resolve <- topLike_super_top : core.

#[export]
Hint Immediate topLike_super_top  toplike_sub : core.


(* subtyping *)
Lemma sub_l_andl : forall A B C, algo_sub A C -> algo_sub (t_and A B) C.
Proof.
  introv s. induction* s.
Qed.

Lemma sub_l_andr : forall A B C, algo_sub B C -> algo_sub (t_and A B) C.
Proof.
  introv s. induction* s.
Qed.

Lemma sub_fun : forall A B C D,
    algo_sub B D -> algo_sub C A -> algo_sub (t_arrow A B) (t_arrow C D).
Proof.
  introv s. induction* s.
Qed.

Lemma sub_rcd : forall A B l,
    algo_sub A B -> algo_sub (t_rcd l A) (t_rcd l B).
Proof.
  introv H.
  induction* H.
Qed.

#[export]
Hint Resolve sub_l_andl sub_l_andr sub_fun sub_rcd: core.

Lemma sub_reflexivity : forall A, algo_sub A A.
Proof.
  introv. induction* A.
Qed.

#[export]
Hint Resolve sub_reflexivity : core.

(* around split and subtyping *)
Lemma spl_sub_l : forall A B C,
    spl A B C -> algo_sub A B.
Proof.
  introv H. induction* H.
Qed.

Lemma spl_sub_r : forall A B C,
    spl A B C -> algo_sub A C.
Proof.
  introv H. induction* H.
Qed.

#[export]
Hint Immediate spl_sub_l spl_sub_r : core.

(* splitting does not lose or add information to a type *)
Lemma split_sub: forall A B C,
    spl A B C -> algo_sub A (t_and B C) /\ algo_sub (t_and B C) A.
Proof with eauto.
  intros A B C H.
  split.
  - lets~: spl_sub_l H. lets~: spl_sub_r H.
    apply~ S_and...
  - induction H...
Qed.

(* generalize S_top to all toplike types *)
Lemma toplike_super_any : forall A B,
    topLike A -> algo_sub B A.
Proof.
  introv TL.
  proper_ind A; auto.
  applys~ S_and H.
  - applys* IHr1.
  - applys* IHr2.
Qed.

#[export]
 Hint Immediate toplike_super_any : core.

(* some subtyping inversion lemmas *)
(* inversion on left split *)
Lemma sub_inversion_split_l : forall T A B C,
    algo_sub T A -> spl T B C -> ord A -> algo_sub B A \/ algo_sub C A.
Proof.
  intros. gen B C.
  induction H; intros; try solve_false; split_unify; eauto.
  - (* arrow *)
    forwards*: IHalgo_sub2.
  - (* rec *)
    forwards*: IHalgo_sub.
Qed.

(* inversion on right split *)
Lemma sub_r_spl_l : forall T A B C,
    algo_sub T A -> spl A B C -> algo_sub T B.
Proof.
  introv Hsub Hspl.
  inverts Hsub; solve_false.
  split_unify.
Qed.

Lemma sub_r_spl_r : forall T A B C,
    algo_sub T A -> spl A B C -> algo_sub T C.
Proof.
  introv Hsub Hspl.
  inverts Hsub; solve_false.
  split_unify.
Qed.

Lemma sub_inversion_split_r : forall A B C D,
    algo_sub A B -> spl B C D -> algo_sub A C /\ algo_sub A D.
Proof with (try solve_false; split_unify).
  introv Hsub Hspl. gen C D.
  inductions Hsub; intros; eauto...
Qed.

#[export]
Hint Immediate sub_r_spl_l sub_r_spl_r : core.

(* prove trans via proper type *)
Lemma sub_transtivity : forall A B C,
    algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof with (try solve_false; split_unify; eauto).
  introv S1 S2. gen A C.
  proper_ind B; intros;
    try solve [inductions S2; eauto].
  - (* arrow *)
    inductions S2... clear IHS2_1 IHS2_2.
    (* S_arr *)
    inductions S1...
    + applys* S_top.
  - (* rcd *)
    inductions S2... clear IHS2.
    (* S_rcd *)
    inductions S1...
    + applys* S_top.
      applys* toplike_sub H1.
  - (* split A B C *)
    gen A B.
    proper_ind C0; (* the type at the end *)
      introv S1 S2 Hspl HRb IH;
      try solve [ (* if it is an ordinary type *)
            forwards~ (?&?): sub_inversion_split_r S1 Hspl;
            forwards~ [?|?]: sub_inversion_split_l S2; eauto ].
    (* splittable type *)
    forwards* (?&?): sub_inversion_split_r S2 H.
Qed.

#[export]
Hint Immediate sub_transtivity : core.

(* any part of a toplike type is a toplike type *)
Example sub_spl_demo : forall A B C,
    algo_sub t_top A -> spl A B C -> algo_sub A B /\ algo_sub A C /\ algo_sub t_top B /\ algo_sub t_top C.
Proof.
  jauto.
Qed.

(******************************************************************************)
(* an alternative proof method *)
(* prove transtivity via typ_size *)
Lemma typ_size_lg_z : forall T, size_typ T > 0.
Proof.
  introv.
  pose proof (size_typ_min) T.
  inverts~ H.
Qed.

Lemma exp_size_lg_z : forall e, size_exp e > 0.
Proof.
  introv.
  pose proof (size_exp_min) e.
  inverts~ H.
Qed.

Ltac eomg :=
  pose proof (typ_size_lg_z);
  pose proof (exp_size_lg_z);
  try lia; auto; simpl in *; try lia.


Lemma split_decrease_size: forall A B C,
    spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  introv H. induction* H; eomg.
Qed.

#[export]
Hint Extern 0 => match goal with
                 | [ H1: topLike (t_arrow _ ?D), H2: ~topLike ?D |- False ] => (
                     inverts H1;
                       contradiction)
                 | [ H: topLike t_int |- False ] => (
                     inverts H )
                 | [ H1: ord ?A, H2: spl (t_arrow _ ?A) _ _ |- False ] => (
                     inverts H2;
                       auto with falseHd)
                 end : falseHd.


Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

#[local]
Hint Extern 0 =>
  match goal with
  | [ IH: forall _ , _ , H1: algo_sub  ?A ?B , H2: algo_sub ?B ?C |- algo_sub ?A ?C ] =>
    (forwards: IH H1 H2; eomg)
  end : core.

Section sub_trans.
Lemma trans : forall A B C, algo_sub A B -> algo_sub B C -> algo_sub A C.
Proof.
  introv s1 s2.
  indTypSize (size_typ A + size_typ B + size_typ C).
  lets [?|(?&?&?)]: ord_or_split C.
  - (* ord C *)
    lets [?|(?&?&?)]: ord_or_split B.
    + (* ord B *)
      inverts keep s2 as s2_1 s2_2 s2_3;
        inverts s1 as s1_1 s1_2 s1_3; solve_false; auto.
      * (* topLike arr *)
        applys* S_top.
      * (* topLike rcd *)
        applys* S_top.
    + (* spl B x x0 *)
      (* splitl_inv turns B into x or x0 *)
      lets (?&?): split_decrease_size B. eauto.
      forwards~ [s2' |s2']: sub_inversion_split_l s2 H0.
      applys* IH s2'. eomg.
      applys* IH s2'. eomg.
  - (* spl C x x0 *)
    (* inversion turns C into x and x0 *)
    lets (?&?): split_decrease_size C. eauto.
    forwards~ g1: IH s1 x. eauto. eomg.
    forwards~ g2: IH s1 x0. eauto. eomg.
    applys~ S_and H.
Qed.

End sub_trans.
(******************************************************************************)

(*
Hint Extern 0 => match goal with
                 | [ |- algo_sub (t_and ?A ?B) ?A ] => apply sub_l_andl
                 | [ |- algo_sub (t_and ?A ?B) ?B ] => apply sub_l_andr
                 | [ H: algo_sub ?A (t_and ?B ?C) |- algo_sub ?A ?B ] => eapply (trans _ (t_and B C))
                 | [ H: algo_sub ?A (t_and ?B ?C) |- algo_sub ?A ?C ] => eapply (trans _ (t_and B C))
                 end : core.
*)

Ltac auto_sub :=
  repeat (auto ;
          match goal with
          | [ |- algo_sub (t_and ?C ?D) (t_and ?A ?B) ] => (eapply S_and; try apply Sp_and)
          | [ |- algo_sub (t_and (t_arrow ?A ?B) (t_arrow ?A ?C)) (t_arrow ?A (t_and ?B ?C)) ] => (eapply S_and)
          | [ H1: algo_sub ?A ?B, H2: algo_sub ?B ?C |- algo_sub ?A ?C ] =>
            (forwards: trans H1 H2; auto)
          | [ H: algo_sub t_top ?A |- algo_sub _ ?A ] =>
            (apply topLike_super_top in H; apply S_top; auto)
          | [ H: topLike ?A |- algo_sub _ (t_arrow _ ?A) ] =>
            (apply TL_arr in H; apply S_top; auto)

          | [ H1: spl ?A ?B ?C, H2: ord ?D, H3: algo_sub ?A ?D |- _ ] => (
              forwards [?|?]: sub_inversion_split_l H1 H2 H3;
              clear H3)
          | [ H1: spl ?A ?B ?C |- _ ] => (
              forwards : split_sub H1;
              forwards : spl_sub_l H1;
              forwards : spl_sub_r H1;
              clear H1)
          | [ |- algo_sub (t_arrow ?A ?B) (t_arrow ?C ?D) ] => apply sub_fun
          | [ H1: algo_sub ?A ?B |- algo_sub ?A ?C ] =>
            assert ( algo_sub B C ) by auto
          end).


(* modular subtyping <=> algorithmic subtyping *)
Theorem modular_sub_eqv: forall A B,
    msub A B <-> algo_sub A B.
Proof.
  split; introv H;
  induction* H.
Qed.
