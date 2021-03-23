Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Typing
               Subtyping_inversion.



(* TypedReduce *)
(*
Fixpoint top_value (A:typ) : exp :=
  match A with
  | t_prod A1 A2 => e_pair (top_value A1) (top_value A2)
  | _ => e_top
  end.

Lemma TypedReduce_ord_toplike_normal : forall (v v': exp) (A : typ),
    ord A -> topLike A -> TypedReduce v A v' -> v' = top_value A.
 *)

Lemma TypedReduce_ord_toplike_normal : forall (v v': exp) (A : typ),
    ord A -> topLike A -> TypedReduce v A v' -> v' = e_top.
Proof.
  introv H1 H2 Red.
  induction~ Red; try solve_false.
Qed.


Lemma TypedReduce_toplike :
  forall A, topLike A ->
            forall (v1 v2 v1' v2' : exp), TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.
Proof.
  intros A Typ.
  induction Typ;
    introv Red1 Red2.
  - forwards~: TypedReduce_ord_toplike_normal Red1.
    forwards~: TypedReduce_ord_toplike_normal Red2.
    subst*.
  - inverts~ Red1; try solve_false;
      inverts~ Red2; try solve_false.
    forwards: IHTyp1 H2 H3.
    forwards: IHTyp2 H4 H6.
    subst*.
  - forwards~: TypedReduce_ord_toplike_normal Red1.
    forwards~: TypedReduce_ord_toplike_normal Red2.
    subst*.
  - forwards~: TypedReduce_ord_toplike_normal Red1.
    forwards~: TypedReduce_ord_toplike_normal Red2.
    subst*.
Qed.


Lemma TypedReduce_sub: forall v v' A B,
    value v -> TypedReduce v A v' -> Typing nil v Inf B -> sub B A.
Proof.
  introv Val Red Pt. gen B.
  induction Red; intros;
    try solve [auto_sub];
    try solve [inverts~ Pt; auto_sub];
    (* merge *)
    inverts~ Val; inverts~ Pt.
Qed.


Lemma disjoint_val_consistent: forall A B v1 v2,
    disjointSpec A B -> value v1 -> value v2 -> Typing nil v1 Inf A -> Typing nil v2 Inf B -> consistencySpec v1 v2.
Proof.
  intros A B v1 v2 Dis Val1 Val2 Typ1 Typ2.
  unfold consistencySpec.
  introv Red1 Red2.
  forwards* Sub1': TypedReduce_sub Red1.
  forwards* Sub2': TypedReduce_sub Red2.
  subst.
  assert (Top: topLike A0). {
    unfold disjointSpec in Dis.
    apply~ Dis.
  }
  forwards*: TypedReduce_toplike Top Red1 Red2.
Qed.
