Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure
        Subtyping_inversion
        Key_Properties
        Deterministic
        rules_inf2
        dunfield.

Require Import Omega.

Lemma open_dexp_eqn_aux :
                forall ee1 ee2 x n,
       x `notin` fv_dexp ee1 ->
       x `notin` fv_dexp ee2 ->
       open_dexp_wrt_dexp_rec n (de_var_f x) ee1 = open_dexp_wrt_dexp_rec n (de_var_f x) ee2
       -> ee1 = ee2.
Proof.
  apply_mutual_ind dexp_mutind;
  apply_mutual_ind dexp_mutind;
  default_simp;
  try solve [eapply_first_hyp; eauto].
  omega.
Qed.

Lemma open_dexp_eqn : forall x ee1 ee2,
       x `notin` fv_dexp ee1 ->
       x `notin` fv_dexp ee2 ->
       open_dexp_wrt_dexp ee1 (de_var_f x) = open_dexp_wrt_dexp ee2 (de_var_f x)
       -> ee1 = ee2.
Proof.
  intros x ee1 ee2 H H0 H1.
  unfold open_dexp_wrt_dexp in H1.
  pose proof open_dexp_eqn_aux.
  eauto.
Qed.

Lemma subtyping_completeness : forall A B,
    isub A B -> sub A B.
Proof.
  intros A B H.
  induction* H.
Qed.

Lemma disjoint_completeness : forall A B,
    icfpDisjoint A B -> disjointSpec A B.
Proof.
  intros A B H. apply disjoint_eqv.
  induction~ H.
  (* H: icfpDisjointAx A B *)
  induction~ H.
  (* symm case *)
  apply disjoint_eqv.
  applys~ disjoint_symmetric.
  apply~ disjoint_eqv.
Qed.


(* completeness of typing with respect to the extended
 bidirectional type system in ICFP 2016 *)
Theorem typing_completeness : forall G ee dir A e,
    IBTyping G ee dir A e -> Typing G e dir A.
Proof.
  intros G ee dir A e Typ.
  induction* Typ.
  - (* abs *)
    eapply Typ_sub. eapply Typ_abs.
    intros. applys* H1 H2.
    apply sub_reflexivity.
  - (* fixpoint *)
    eapply Typ_sub. eapply Typ_fix.
    intros. applys* H1 H2.
    apply sub_reflexivity.
Qed.
