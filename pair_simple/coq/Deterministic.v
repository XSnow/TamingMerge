Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure
        Key_Properties
        Subtyping_inversion.

Require Import Strings.String.


(* if we want to build determinism on the right typing strictly, then we need to prove some lemma like A*B -> A&B <: C -> .|-v1,,v2:A&B -> v1 ~->C v1' -> A <: C *)
(* then we might be able to drop the subtyping checking in tred *)
Lemma TypedReduce_unique: forall (v v1 v2 : exp) (A: typ),
    value v -> (exists B, Typing nil v Inf B) -> TypedReduce v A v1 -> TypedReduce v A v2 -> v1 = v2.
Proof.
  intros v v1 v2 A Val H R1 R2.
  gen v2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts~ R2; try solve_false];
    try solve [forwards*: TypedReduce_toplike R1' R2].
  - (* mergel *)
    lets [B H']: H.
    lets R2': R2.
    inverts Val.
    inverts* R2;
      try solve [forwards*: TypedReduce_toplike R1 R2'];
      try solve [inverts* H'].
    +
      inverts* H'.
      forwards* Con: disjoint_val_consistent H12 H8 H11.
    +
      inverts* H1.
  - (* merger *)
    lets [B H']: H.
    lets R2': R2.
    inverts Val.
    inverts* R2;
      try solve [forwards*: TypedReduce_toplike R1 R2'];
      try solve [inverts* H'].
    +
      inverts* H'.
      forwards* Con: disjoint_val_consistent H12 H8 H11.
      forwards*: Con H7 R1.
      forwards*: H14 H7 R1.
    +
      inverts* H1.
  - (* and *)
    inverts~ R2; try solve_false.
    forwards*: IHR1_1.
    forwards*: IHR1_2.
    congruence.
  - (* prod *)
    inverts Val. inverts H. inverts H1.
    inverts~ R2; try solve_false.
    forwards*: IHR1_1.
    forwards*: IHR1_2.
    congruence.
Qed.


Theorem step_unique: forall A (e e1 e2 : exp),
    Typing nil e Chk A -> step e e1 -> step e e2 -> e1 = e2.
Proof.
  introv Typ Red1.
  gen A e2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* topApp *)
    inverts* Red2.
    + inverts H4.
    + forwards*: step_not_value H4.
  - (* topProjl *)
    inverts* Red2. inverts H0.
  - (* topProjr *)
    inverts* Red2. inverts H0.
  - (* beta *)
    inverts* Red2.
    + (* beta *)
      inverts* Typ. inverts H2.
      inverts H11.
      * (* arrow *)
        lets* (?&?): Typing_chk2inf H12. (* Typing condition for the following assert *)
        assert (v' = v'0) by forwards*: TypedReduce_unique H1 H9.
        congruence.
      * (* top *)
        lets* (?&?): Typing_chk2inf H12. (* Typing condition for the following assert *)
        assert (v' = v'0) by forwards*: TypedReduce_unique H1 H9.
        congruence.
    + (* app1 *)
      inverts* H6.
    + (* app2 *)
      forwards*: step_not_value H6.
  - (* annov *)
    inverts* Red2.
    + (* annov *)
      forwards*: TypedReduce_unique H0 H5.
      inverts* Typ. inverts* H1.
      lets* (?&?): Typing_chk2inf H7.
    + (* anno *)
      forwards*: step_not_value H4.
  - (* appl *)
    inverts* Red2.
    + (* top *)
      forwards*: step_not_value Red1.
    + (* absv *)
      forwards*: step_not_value Red1.
    + (* appl *)
      inverts* Typ. inverts H0.
      forwards*: IHRed1. subst~.
    + (* appr *)
      forwards*: step_not_value Red1.
  - (* appr *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* appl *)
      forwards*: step_not_value H4.
    + (* appr *)
      inverts* Typ. inverts H0.
      forwards*: IHRed1.
      congruence.
  - (* mergel *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* mergel *)
      inverts* Typ; inverts H0;
        forwards*: IHRed1;
        congruence.
  - (* merger *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* mergel *)
      forwards*: step_not_value H4.
    + (* merger *)
      inverts* Typ; inverts H0;
        forwards*: IHRed1;
        congruence.
  - (* pairl *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* pairl *)
      inverts* Typ; inverts H0;
        forwards*: IHRed1;
        congruence.
  - (* pairr *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* pairl *)
      forwards*: step_not_value H4.
    + (* pairr *)
      inverts* Typ; inverts H0;
        forwards*: IHRed1;
        congruence.
  - (* projl *)
    inverts* Red2.
    + (* top *)
      forwards*: step_not_value Red1.
    + (* projl *)
      inverts Typ. inverts H.
      forwards*: IHRed1. subst~.
    + (* projlv *)
      forwards*: step_not_value Red1.
  - (* projlv *)
    inverts Typ. inverts~ Red2.
    forwards*: step_not_value H4.
  - (* projr *)
    inverts* Red2;
      try solve [forwards*: step_not_value Red1].
    + (* merger *)
      inverts* Typ. inverts H.
      forwards*: IHRed1.
      congruence.
  - (* projrv *)
    inverts Typ. inverts~ Red2.
    forwards*: step_not_value H4.
  - (* anno *)
    inverts* Red2;
      inverts* Typ; inverts H;
      try solve [inverts* Red1];
      try solve [lets*: step_not_value Red1].
    forwards*: IHRed1.
    congruence.
  - (* fix *)
    inverts* Red2.
Qed.
