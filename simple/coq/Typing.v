Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Subtyping_inversion
               Infrastructure.

Require Import List. Import ListNotations.


(* Check Mode *)
Lemma Typing_chk2inf: forall G v A,
    Typing G v Chk A -> exists B, Typing G v Inf B /\ sub B A.
Proof.
  intros G v A Typ.
  inductions Typ; try solve [inverts Val].
  exists.
  split*.
Qed.


Lemma Typing_chk_sub: forall G e A B,
    Typing G e Chk A -> sub A B -> Typing G e Chk B.
Proof.
  intros G e A B H H0.
  inductions H.
  - eapply Typ_sub.
    apply H.
    auto_sub.
Qed.


(* Common Lemmas *)
Lemma Typing_regular_1 : forall e G dir A,
    Typing G e dir A -> lc_exp e.
Proof.
  intros e G dir A H.
  induction H;
    eauto.
Qed.

Lemma Typing_regular_2 : forall G e dir T,
    Typing G e dir T -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.

  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.


Lemma Typing_weaken : forall G E F e dir T,
    Typing (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    Typing (E ++ F ++ G) e dir T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply Typ_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* fix *)
      pick fresh x and apply Typ_fix.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma Typing_weakening : forall (E F : ctx) e dir T,
    Typing E e dir T ->
    uniq (F ++ E) ->
    Typing (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weaken.
Qed.


(** Typing is preserved by substitution. *)

Lemma fv_in_dom: forall G e dir T,
    Typing G e dir T -> fv_exp e [<=] dom G.
Proof.
  intros G e dir T H.
  induction H; simpl; try fsetdec.
  - (* typing_var *)
    apply binds_In in H0.
    fsetdec.
  - (* typing_abs *)
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - (* typing_fix *)
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma value_no_fv : forall v dir T,
    Typing [] v dir T -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.

Lemma subst_value : forall v T dir z u,
    Typing [] v dir T -> subst_exp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma Typing_subst_2 : forall (E F : ctx) e u S S' dir T (z : atom),
    Typing (F ++ [(z,S)] ++ E) e dir T ->
    Typing E u Inf S' ->
    subsub S' S ->
    exists T', Typing (F ++ E) ([z ~> u] e) dir T' /\ subsub T' T.
Proof.
  introv Typ Typv Subsub.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  inductions Typ;
    intros F Eq; subst; simpl; autos*;
      lets Lc  : Typing_regular_1 Typv;
      lets Uni : Typing_regular_2 Typv;
      try solve [exists; split*].
  - (* var *)
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    exists. split.
    apply~ Typing_weakening. eauto.
    solve_uniq.
    auto.
  - (* abs *)
    exists. split.
    eapply (Typ_abs (union L (singleton z))); eauto.
    intros.
    forwards~(?&?&?): H0 x.
    rewrite_env (([(x, A)] ++ F) ++ [(z, S)] ++ E).
    reflexivity.
    (* lc_e_abs_exists *)
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply subsub2sub in H3.
    forwards*: Typing_chk_sub H2 H3.
    auto.
  - (* app *)
    forwards* (?&?&?): IHTyp1.
    forwards* (?&?&?): IHTyp2.
    inverts H.
    + (* arrow *)
      apply subsub2sub in H3.
      inverts H1.
    * exists B. split*.
      forwards~: Typing_chk_sub H2 H3.
      forwards*: Typ_app H.
    * exists A2. split*.
      assert (HS: sub x0 A1) by auto_sub.
      forwards~: Typing_chk_sub H2 HS.
      forwards*: Typ_app H.
    * (* toplike *)
      exists t_top. split*.
      ** applys* Typ_app H0.
         applys* Typing_chk_sub H2.
      ** inverts~ H.
    + (* T v *)
      exists t_top. split*.
      applys* Typ_app H0.
      inverts~ H1; inverts~ H3.
  - (* merge *)
    forwards* (?&?&?): IHTyp1.
    forwards* (?&?&?): IHTyp2.
    exists (t_and x x0). split*.
    apply~ Typ_merge.
    eapply subsub_disjointSpec_l. eassumption.
    eapply subsub_disjointSpec_r. eassumption.
    assumption.
  - (* anno *)
    exists A. split*.
    apply Typ_anno.
    forwards* (?&?&?): IHTyp.
    apply subsub2sub in H0.
    forwards*: Typing_chk_sub H H0.
  - (* fix *)
    exists A. split*.
    pick fresh x and apply Typ_fix.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    forwards* (?&?&?): H0.
    rewrite_env (([(x, A)] ++ F) ++ [(z, S)] ++ E).
    reflexivity.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply subsub2sub in H2.
    forwards*: Typing_chk_sub H1 H2.
  - (* mergev *)
    lets Eq1: ((subst_value _ _ _ z u) Typ1).
    lets Eq2: ((subst_value _ _ _ z u) Typ2).
    rewrite Eq1.
    rewrite Eq2.
    exists (t_and A B). split*.
  - (* sub *)
    forwards* (?&?&?): IHTyp.
    exists B. split*.
    apply subsub2sub in H1.
    assert (sub x B) by auto_sub.
    forwards*: Typ_sub H0 H1.
Qed.

(* stronger than inf unique *)
Lemma Typing_strenthening : forall G e A1 A2,
    []  ⊢ e ⇒ A1 ->
    G ⊢ e ⇒ A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 G.
  inductions Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    inverts H0.
  - (* t_app *)
    forwards * : IHTy1_1 H2. subst.
    forwards*: arrTyp_unique H H4. inverts~ H0.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_and *)
    forwards * HT1: Typing_weakening G H4.
    forwards * HT2: Typing_weakening G H6.
    rewrite app_nil_r in HT1.
    rewrite app_nil_r in HT2.
    forwards * : IHTy1_1 HT1.
    substs.
    forwards * : IHTy1_2 HT2.
    substs*.
  - (* t_and *)
    forwards * HT1: IHTy1_1 H4.
    forwards * HT2: IHTy1_2 H6.
    substs*.
  - (* t_and *)
    forwards * : IHTy1_1 H6.
    forwards * : IHTy1_2 H8.
    substs*.
Qed.

Lemma inference_unique : forall G e A1 A2,
    Typing G e Inf A1 ->
    Typing G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H2. subst.
    forwards*: arrTyp_unique H H4. inverts H0.
    forwards * : IHTy1_1 H2.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_and *)
    forwards * HT1: Typing_weakening G H4.
    forwards * HT2: Typing_weakening G H6.
    rewrite app_nil_r in HT1.
    rewrite app_nil_r in HT2.
    forwards * : IHTy1_1 HT1.
    substs.
    forwards * : IHTy1_2 HT2.
    substs*.
  - (* t_and *)
    forwards* HT1: Typing_strenthening Ty1_1 H4.
    forwards* HT2: Typing_strenthening Ty1_2 H6.
    subst*.
  - (* t_and *)
    forwards *: IHTy1_1 H6.
    forwards *: IHTy1_2 H8.
    substs*.
Qed.


(* Infer Mode & Check Mode *)
Lemma Typing_inf_chk_sub: forall G e A B,
    Typing G e Inf A -> Typing G e Chk B -> sub A B.
Proof.
  intros G e A B H H0.
  lets (?&?&?): Typing_chk2inf H0.
  lets : inference_unique H H1.
  subst*.
Qed.
