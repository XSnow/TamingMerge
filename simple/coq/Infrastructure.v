Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.


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

Hint Constructors star.

Hint Resolve star_trans star_one.


Definition mul_dstep := star dexp DunfieldStep.
Notation "e ->>* e'" := ((star dexp DunfieldStep) e e') (at level 68).

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


Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
Qed.

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


Lemma multi_red_app1 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* t1' -> (e_app t1 t2) ->* (e_app t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_app2 : forall v t t',
    value v -> lc_exp v -> t ->* t' -> (e_app v t) ->* (e_app v t').
Proof.
  introv Val ? Red.
  induction* Red.
Qed.


Lemma multi_red_merge1 : forall t1 t2 t1',
    lc_exp t2 ->
    t1 ->* t1' ->
    (e_merge t1 t2) ->* (e_merge t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_merge2 : forall v1 t2 t2',
    value v1 -> lc_exp v1 ->
    t2 ->* t2' ->
    (e_merge v1 t2) ->* (e_merge v1 t2').
Proof.
  introv Val ? Red.
  induction* Red.
Qed.


Lemma multi_red_merge3 : forall t1 t2 v1 v2,
    value v1 -> value v2 -> lc_exp v1 -> lc_exp t2 ->
    t1 ->* v1 -> t2 ->* v2 ->
    (e_merge t1 t2) ->* (e_merge v1 v2).
Proof.
  intros.
  apply star_trans with (b := e_merge v1 t2).
  sapply* multi_red_merge1.
  sapply* multi_red_merge2.
Qed.


(** Typing is preserved by substitution. *)



(* doesn't hold in two anno *) (*
Lemma typing_uniq: forall G e A B,
    G |= e ~: A -> G |= e ~: B -> A = B.
Proof.
  intros G e A B Typ1 Typ2.
  gen B.
  induction Typ1;
    introv Typ2;
    try solve [inverts* Typ2].
  - inverts* Typ2.
    gen B.
    induction H0;
      introv Typ2;
      inverts* Typ2.
    forwards*: IHVtyping1.
    forwards*: IHVtyping2.
    congruence.
  - (* f_var *)
    inverts* Typ2.
    forwards*: binds_unique H0 H4 H2.
  - (* e_app *)
    inverts* Typ2.
    forwards*: IHTyp1_1.
    forwards*: IHTyp1_2.
    subst.
    inverts* H0.
  - (* and *)
    inverts* Typ2.
    forwards*: IHTyp1_1.
    forwards*: IHTyp1_2.
    congruence.
Qed.
*)

(* typing canonical *)
