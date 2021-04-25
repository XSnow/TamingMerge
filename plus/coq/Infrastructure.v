Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Export syntax_ott.
Require Import
        rules_inf
        SubtypingInversion
        Disjointness.

Require Import List. Import ListNotations.


Definition relation (X:Type) := X -> X -> Prop.

Section Star.

  Variable A : Type.
  Variable R : relation A.

  Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b b',
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros. destruct (star_star_inv _ _ H _ H1).
    - inversion H3; subst. auto. elim (H0 _ H4).
    - inversion H3; subst. auto. elim (H2 _ H4).
  Qed.


End Star.

#[export] Hint Constructors star : core.

#[export] Hint Resolve star_trans star_one : core.



Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).

Notation "R 'star'" := (star exp R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).
(*
Definition typed e A : Prop := Dtyping nil e A.
Definition well_typed e : Prop := exists A, Dtyping nil e A.
*)
(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)


Lemma value_merge_l_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v1.
Proof.
  introv H.
  inverts~ H.
Qed.

Lemma value_merge_r_inv : forall v1 v2,
    value (e_merge v1 v2) -> value v2.
Proof.
  introv H.
  inverts~ H.
Qed.

Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
Qed.


Lemma TypedReduce_prv_value: forall v A v',
    value v -> TypedReduce v A v' -> value v'.
Proof.
  intros v A v' Val Red.
  induction* Red.
  - apply value_anno.
    inverts* H.
  - inverts* Val.
  - inverts* Val.
  - inverts* Val.
Qed.

#[export] Hint Immediate value_merge_l_inv value_merge_r_inv value_lc TypedReduce_prv_value : core.


Lemma step_not_value: forall (v:exp),
    value v -> irred exp step v.
Proof.
  introv.
  unfold irred.
  induction v; introv H;
    inverts* H;
    unfold not;
    intros;
    inverts* H.
Qed.


Lemma value_no_step : forall (v t: exp),
    value v -> v ->* t -> v = t.
Proof.
  introv Val Red.
  induction* Red.
  lets : step_not_value Val H.
  tryfalse.
Qed.


#[export] Hint Extern 0 => try match goal with
                     | [ H: value (e_anno _ _) |- _ ] =>
                       inverts H
                     | [ H: value (e_app _ _) |- _ ] =>
                       inverts H
                     | [ H: value (e_fixpoint _ _) |- _ ] =>
                       inverts H
                     | [ H1: step ?e _, H2: value ?e |- _ ] =>
                       forwards: step_not_value H2 H1
                     | [ H1: step (e_lit _) _ |- _ ] =>
                       forwards: step_not_value H1
                     | [ H1: step (e_abs _ ?e _) _ |- _ ] =>
                       forwards: step_not_value H1
                     | [ H1: step e_top _ |- _ ] =>
                       forwards: step_not_value H1
                     end : falseHd.
(* lc *)
Lemma abs_lc_inv : forall e A B A' B',
    lc_exp (e_abs A e B) -> lc_exp (e_abs A' e B').
Proof.
  introv H.
  inverts~ H.
Qed.

Lemma abs_lc_open : forall e A B v,
    lc_exp (e_abs A e B) -> lc_exp v -> lc_exp (e ^^ v).
Proof.
  intros e A B v H H0.
  inverts H.
  apply~ lc_body_exp_wrt_exp.
Qed.

#[export] Hint Immediate abs_lc_inv : core.
#[export] Hint Resolve abs_lc_open: core.

Lemma TypedReduce_l_lc : forall v1 A v2,
    TypedReduce v1 A v2 -> lc_exp v1.
Proof.
  intros v1 A v2 H.
  induction~ H.
Qed.

Lemma TypedReduce_r_lc : forall v1 A v2,
    TypedReduce v1 A v2 -> lc_exp v2.
Proof.
  intros v1 A v2 H.
  induction* H.
Qed.

#[export] Hint Immediate TypedReduce_l_lc TypedReduce_r_lc : core.

Lemma papp_1_lc: forall v1 v2 e,
    papp v1 v2 e -> lc_exp v1.
Proof.
  intros v1 v2 e H.
  induction~ H.
Qed.

Lemma papp_2_lc: forall v1 v2 e,
    papp v1 (vl_exp v2) e -> lc_exp v2.
Proof.
  intros v1 v2 e H.
  inductions H; eauto.
  inverts~ H.
Qed.

Lemma papp_3_lc: forall v1 v2 e,
    papp v1 v2 e -> lc_exp e.
Proof.
  intros v1 v2 e H.
  induction* H.
Qed.

#[export] Hint Immediate papp_1_lc papp_2_lc papp_3_lc : core.

Lemma step_1_lc: forall e1 e2,
    step e1 e2 -> lc_exp e1.
Proof.
  intros e1 e2 H.
  induction~ H.
Qed.

Lemma step_2_lc: forall e1 e2,
    step e1 e2 -> lc_exp e2.
Proof.
  intros e1 e2 H.
  induction* H.
  inverts H.
  constructor.
  apply~ lc_body_exp_wrt_exp.
Qed.

#[export] Hint Immediate step_1_lc step_2_lc : core.


Lemma step_prv_prevalue : forall u1 u2,
    step u1 u2 -> prevalue u1 -> prevalue u2.
Proof.
  intros u1 u2 st p. gen u2.
  induction p; try solve [intros; inverts* st].
  - (* val *)
    induction H; intros; inverts st; solve_false.
Qed.

Lemma consistent_prevalue1 : forall u1 u2,
    consistent u1 u2 -> prevalue u1.
Proof.
  intros u1 u2 H.
  induction~ H.
Qed.

Lemma consistent_prevalue2 : forall u1 u2,
    consistent u1 u2 -> prevalue u2.
Proof.
  intros u1 u2 H.
  induction~ H. inverts* H.
Qed.

#[export] Hint Immediate step_prv_prevalue consistent_prevalue1 consistent_prevalue2: core.


(* Check Mode *)
Lemma Typing_chk2inf: forall G v A,
    Typing G v Chk A -> exists B, Typing G v Inf B /\ algo_sub B A.
Proof.
  intros G v A Typ.
  inductions Typ; try solve [inverts Val].
  exists.
  split*.
Qed.


Lemma Typing_chk_sub: forall G e A B,
    Typing G e Chk A -> algo_sub A B -> Typing G e Chk B.
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

#[export] Hint Immediate Typing_regular_1 Typing_regular_2 : core.

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
  - (* typing_var*)
    apply binds_In in H0.
    fsetdec.
  - (* typing_abs*)
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - (* typing_fix*)
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

#[local] Hint Resolve subsub_refl : core.

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
    forwards* (?&?&?&?): arrTyp_arr_subsub H H1.
    forwards* (?&?): subsub_arr_inv H5.
    apply subsub2sub in H3.
    lets* Sub: trans H3 H6.
    forwards*: Typing_chk_sub H2 Sub.
  - (* proj *)
    forwards* (?&?&?): IHTyp.
    forwards* (?&?&?): arrTyp_rcd_subsub H H1.
    forwards* (?&?): subsub_rcd_inv H3.
  - (* rcd *)
    forwards* (?&?&?): IHTyp.
  - (* merge *)
    forwards* (?&?&?): IHTyp1.
    forwards* (?&?&?): IHTyp2.
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
    eauto.
  - (* algo_sub *)
    forwards* (?&?&?): IHTyp.
    exists B. split*.
    apply subsub2sub in H1.
    assert (algo_sub x B) by auto_sub.
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
    forwards * : IHTy1_1 H2. subst*.
    forwards * : arrTyp_arrow_unique H H4.
  - (* proj *)
    forwards*: IHTy1. subst. forwards*: arrTyp_rcd_unique H H4.
  - (* rcd *)
    forwards*: IHTy1. subst*.
  - (* merge *)
    forwards * : IHTy1_1 H2.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* disjoint -> consistent *)
    forwards * : IHTy1_1 H3.
    forwards * : IHTy1_2 H5.
    substs*.
  - (* consistent -> disjoint *)
    forwards * : IHTy1_1 H3.
    forwards * : IHTy1_2 H5.
    substs*.
  - (* consistent -> consistent *)
    forwards * : IHTy1_1 H4.
    forwards * : IHTy1_2 H6.
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
    forwards * : IHTy1_1 H2. subst*.
    forwards * : arrTyp_arrow_unique H H4.
  - (* t_proj *)
    forwards * : IHTy1 H3. subst*.
    forwards * : arrTyp_rcd_unique H H4.
  - (* t_rcd *)
    forwards * : IHTy1 H1.
    subst*.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_and *)
    forwards * HT1: Typing_weakening G H3.
    forwards * HT2: Typing_weakening G H5.
    rewrite app_nil_r in HT1.
    rewrite app_nil_r in HT2.
    forwards * : IHTy1_1 HT1.
    substs.
    forwards * : IHTy1_2 HT2.
    substs*.
  - (* t_and *)
    forwards* HT1: Typing_strenthening Ty1_1 H3.
    forwards* HT2: Typing_strenthening Ty1_2 H5.
    subst*.
  - (* t_and *)
    forwards *: IHTy1_1 H4.
    forwards *: IHTy1_2 H6.
    substs*.
Qed.


(* Infer Mode & Check Mode *)
Lemma Typing_inf_chk_sub: forall G e A B,
    Typing G e Inf A -> Typing G e Chk B -> algo_sub A B.
Proof.
  intros G e A B H H0.
  lets (?&?&?): Typing_chk2inf H0.
  lets : inference_unique H H1.
  subst*.
Qed.


(* Typing Equivalence *)
Lemma Typing_app_subsume : forall G e1 e2 A B,
    Typing G e1 Inf (t_arrow A B) -> Typing G e2 Chk A -> Typing G (e_app e1 e2) Inf B.
Proof.
  intros G e1 e2 A B t1 t2.
  eauto.
Qed.

#[export] Hint Immediate Typing_inf_chk_sub Typing_chk_sub Typing_app_subsume : core.
