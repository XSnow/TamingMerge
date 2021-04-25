Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Disjoint_n_toplike
        Subtyping_inversion
        Key_Properties.

Require Import Arith Lia.


Lemma TypedReduce_disjoint_unique: forall (v1 v2 v1' v2': exp) (A A' B B' C: typ),
    value v1 -> value v2 ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B ->
    pType v1 A' -> pType v2 B' -> disjoint A' B' ->
    TypedReduce v1 C v1' -> TypedReduce v2 C v2' ->
    consistent v1 v2 -> v1' = v2'.
Proof with (solve_false; auto).
  intros v1 v2 v1' v2' A A' B B' C Val1 Val2 Typ1 Typ2 pTyp1 pTyp2 Dis R1 R2 Cons.
      forwards*: principal_type_checks v1.
      forwards*: principal_type_checks v2.
      subst.
      forwards* S1: TypedReduce_sub R1.
      forwards* S2: TypedReduce_sub R2.
      apply disjoint_eqv in Dis.
      forwards*: Dis S1 S2.
      forwards*: TypedReduce_toplike R1 R2.
Qed.

Lemma TypedReduce_unique: forall (v1 v2 v1' v2': exp) (A B C: typ),
    value v1 -> value v2 ->
    Typing nil v1 Inf A -> Typing nil v2 Inf B ->
    TypedReduce v1 C v1' -> TypedReduce v2 C v2' ->
    consistent v1 v2 -> v1' = v2'.
Proof with (lia; auto).
  intros v1 v2 v1' v2' A B C Val1 Val2 Typ1 Typ2 R1 R2 Cons.
  gen A B v1 v2 v1' v2'. indTypSize (size_typ C).
  lets [?|(?&?&?)]: ord_or_split C.
  - (* ord *)
    gen A B. induction Cons; intros;
      try solve [
              inverts keep R1;
              try solve [forwards: TypedReduce_toplike R1 R2; try eassumption; auto 4];
              inverts keep R2;
              try solve [forwards~: TypedReduce_toplike R1 R2; try eassumption; auto 4];
              solve_false; auto 4].
    + (* rcd *)
      inverts Val1. inverts Typ1.
      inverts Val2. inverts Typ2.
      inverts keep R1; try solve [forwards~: TypedReduce_toplike R1 R2];
        inverts keep R2; try solve [forwards~: TypedReduce_toplike R1 R2];
          solve_false; auto.
      simpl in SizeInd. forwards*: IH H10 H13. lia. congruence.
    + (* disjoint *)
      forwards*: principal_type_checks u1. forwards*: principal_type_checks u2.
      subst.
      forwards* S1: TypedReduce_sub R1.
      forwards* S2: TypedReduce_sub R2.
      apply disjoint_eqv in H2. forwards*: H2 S1 S2.
      forwards*: TypedReduce_toplike R1 R2.
    +
      inverts Val1.
      inverts keep R1; try solve [forwards~: TypedReduce_toplike R1 R2]; solve_false; auto.
      inverts Typ1; forwards*: IHCons1.
      inverts Typ1; forwards*: IHCons2.
    +
      inverts Val2.
      inverts keep R2; try solve [forwards*: TypedReduce_toplike R1 R2]; solve_false; auto.
      inverts Typ2; forwards*: IHCons1.
      inverts Typ2; forwards*: IHCons2.
  - intros.
    inverts keep R1; try solve [forwards*: TypedReduce_toplike R1 R2]; solve_false; auto.
    inverts keep R2; try solve [forwards*: TypedReduce_toplike R1 R2]; solve_false; auto.
    split_unify.
    assert (HS: forall A B C, spl A B C -> size_typ B < size_typ A /\ size_typ C < size_typ A). {
      intros. induction H0; simpl; try lia.
    }
    lets* (?&?): HS H.
    forwards*: IH H1 H4. lia. forwards*: IH H2 H5. lia.
    subst*.
Qed.


Lemma papp_unique: forall v1 v2 e1 e2 A,
    value v1 -> value v2 -> Typing nil (e_app v1 v2) Inf A -> papp v1 (vl_exp v2) e1 -> papp v1 (vl_exp v2) e2 -> e1 = e2.
Proof with eauto.
  intros v1 v2 e1 e2 A Val1 Val2 Typ P1 P2.
  gen e2 A.
  inductions P1; intros; inverts* P2.
  - inverts Typ. lets (?&?&?): Typing_chk2inf H8.
    forwards*: TypedReduce_unique H0 H7. congruence.
  - inverts Val1.
    inverts Typ.
    lets (?&?&?): Typing_chk2inf H8.
    inverts H5; inverts H7;
      forwards*: IHP1_1 H1;
      forwards*: IHP1_2 H4;
      subst*.
Qed.

Lemma papp_unique2: forall v1 la e1 e2 A,
    value v1 -> Typing nil (e_proj v1 la) Inf A -> papp v1 (vl_la la) e1 -> papp v1 (vl_la la) e2 -> e1 = e2.
Proof with eauto.
  intros v1 la e1 e2 A Val1 Typ P1 P2. gen e2 A.
  inductions P1; intros; inverts* P2.
  - inverts Val1.
    inverts Typ.
    inverts H6;
      inverts H7;
      forwards*: IHP1_1 H1;
      forwards*: IHP1_2 H4;
      subst*.
Qed.

Theorem step_unique: forall A (e e1 e2 : exp),
    Typing nil e Inf A -> step e e1 -> step e e2 -> e1 = e2.
Proof with eauto.
  introv Typ Red1.
  gen A e2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* papp*)
    inverts* Red2.
    + forwards*: papp_unique H1 H7.
    + forwards*: step_not_value H6.
    + forwards*: step_not_value H6.
  - (* proj*)
    inverts* Red2.
    + forwards*: papp_unique2 H0 H5.
    + forwards*: step_not_value H4.
  - (* annov*)
    inverts* Red2.
    + (* annov*)
      inverts* Typ.
      inverts H4.
      forwards*: TypedReduce_unique H0 H5.
    + (* anno*)
      forwards*: step_not_value H4.
  - (* appl*)
    inverts Red2;
      try solve [forwards*: step_not_value Red1].
    + (* appl*)
      inverts Typ.
      forwards: IHRed1...
      congruence.
  - (* appr*)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* appl*)
      forwards*: step_not_value H4.
    + (* appr*)
      inverts* Typ. lets (?&?&?): Typing_chk2inf H7.
      forwards*: IHRed1.
      congruence.
  - (* merge*)
    inverts Typ;
      inverts* Red2;
      try solve [forwards*: step_not_value Red1_2];
      try solve [forwards*: step_not_value Red1_1];
      forwards*: IHRed1_1;
      forwards*: IHRed1_2;
      subst*.
  - (* mergel*)
    inverts* Red2;
      try solve [forwards*: step_not_value H4].
    + (* mergel*)
      inverts* Typ;
        forwards*: IHRed1;
        congruence.
  - (* merger*)
    inverts* Red2;
      try solve [forwards*: step_not_value H2].
    + (* mergel*)
      forwards*: step_not_value H4.
    + (* merger*)
      inverts* Typ;
        forwards*: IHRed1;
        congruence.
  - (* anno*)
    inverts* Red2;
      inverts* Typ;
      try solve [inverts* Red1];
      try solve [lets*: step_not_value Red1].
    inverts H1.
    forwards*: IHRed1.
    congruence.
  - (* fix*)
    inverts* Red2.
  - (* rcd*)
    inverts* Typ. inverts* Red2. forwards*: IHRed1. congruence.
  - (* proj*)
    inverts* Typ. inverts* Red2; try solve [forwards*: step_not_value Red1]. forwards*: IHRed1. congruence.
Qed.
