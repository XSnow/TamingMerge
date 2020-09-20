Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Key_Properties
        Subtyping_inversion
        Disjoint_n_toplike.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.



(* to adjust the subtyping rules can make it easier*)
Lemma TypedReduce_progress: forall v A,
    value v -> Typing [] v Chk A -> exists v', TypedReduce v A v'.
Proof with eauto.
  intros v A Val TypC.
  lets* (B&Typ&Sub): Typing_chk2inf TypC. clear TypC. gen v.
  induction Sub; intros;
    try solve [inverts Typ; inverts Val; exists~].
  - inverts Typ; inverts Val...
    +
      forwards* (?&?): IHSub H2.
    +
      forwards* (?&?): IHSub H4.
  - inverts Typ; inverts~ Val.
    + forwards* (?&?): IHSub H4.
    + forwards* (?&?): IHSub H6.
  - lets *[?|?]: toplike_decidable D.
    +
      clear IHSub1 IHSub2. gen C.
      induction v; intros; inverts Typ; try solve [inverts Val]...
  - lets *[?|?]: toplike_decidable D.
    inverts Typ; inverts Val.
    forwards* (?&?): IHSub H5.
  -
    forwards* (?&?): IHSub1 Typ.
    forwards* (?&?): IHSub2 Typ.
Qed.


Lemma papp_progress: forall v1 v2 A,
    value v1 -> value v2 -> Typing nil (e_app v1 v2) Inf A -> exists e, papp v1 (vl_exp v2) e.
Proof with eauto.
  intros v1 v2 A Val1 Val2 Typ. gen A.
  induction Val1; intros;
    try solve [exists*].
  - inverts Typ.
    inverts H1. inverts H3.
  - inverts Typ. inverts H2.
    inverts H4.
    forwards* (?&?): TypedReduce_progress Val2.
  - inverts Typ.
    inverts H1; inverts H3...
    + assert (sub (t_and A2 B2) A2) by auto_sub.
      assert (sub (t_and A2 B2) B2) by auto_sub.
      forwards*: Typ_app v1 v2.
      forwards*: Typ_app v0 v2.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
    + assert (sub (t_and A2 B2) A2) by auto_sub.
      assert (sub (t_and A2 B2) B2) by auto_sub.
      forwards*: Typ_app v1 v2.
      forwards*: Typ_app v0 v2.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
  - inverts Typ. inverts H1.
    inverts H3.
Qed.


Lemma papp_progress2: forall v1 la A,
    value v1 -> Typing nil (e_proj v1 la) Inf A -> exists e, papp v1 (vl_la la) e.
Proof with eauto.
  intros v1 la A Val1 Typ. gen A.
  induction Val1; intros;
    try solve [exists*].
  - inverts Typ. inverts H2. inverts H3.
  - inverts Typ. inverts H3. inverts H4.
  - inverts Typ.
    inverts H2; inverts H3...
    + lets*: Typ_proj v1 la H4.
      lets*: Typ_proj v2 la H8.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
    + lets*: Typ_proj v1 la H5.
      lets*: Typ_proj v2 la H9.
      forwards* (?&?): IHVal1_1.
      forwards* (?&?): IHVal1_2.
  - inverts Typ. inverts H2. inverts* H3.
Qed.


Theorem progress : forall e dir A,
    Typing nil e dir A ->
    value e \/ exists e', step e e'.
Proof with auto.
  introv Typ. lets Typ': Typ.
  inductions Typ;
    lets Lc: Typing_regular_1 Typ';
    auto;
    try solve [left; auto];
    try solve [right; auto].
  - Case "var".
    invert H0.
  - Case "app".
    inverts Lc.
    right.
    destruct~ IHTyp1 as [Val1 | [e1' Red1]].
    destruct~ IHTyp2 as [Val2 | [e2' Red2]].
    + (* v1 v2 *)
      forwards* (?&?): papp_progress Val1 Val2.
    + exists*.
    + exists*.
  - Case "proj".
    inverts Lc.
    right.
    destruct~ IHTyp as [Val1 | [e1' Red1]].
    + forwards* (?&?): papp_progress2 Val1.
    + exists*.
  - Case "rcd".
    inverts Lc.
    destruct~ IHTyp as [ Val1 | [t1' Red1]]. right*.
  - Case "merge".
    inverts Lc.
    destruct~ IHTyp1 as [ Val1 | [t1' Red1]];
      destruct~ IHTyp2 as [ Val2 | [t2' Red2]];
      subst.
    + SCase "e_merge v1 e2".
      inverts* Typ1.
    + SCase "e_merge e1 v2".
      inverts* Typ2.
    + SCase "e_merge e1 e2".
      inverts* Typ2.
  - Case "anno".
    right.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      lets* (v1' & Tyr) : TypedReduce_progress Val Typ.
    + SCase "e_anno e A".
      forwards*: Step_anno Red.
  - Case "fixpoint".
    right. eauto.
  - Case "mergev".
    destruct~ IHTyp1 as [ Val1 | [t1' Red1]];
      destruct~ IHTyp2 as [ Val2 | [t2' Red2]];
      subst.
    + SCase "e_merge v1 e2".
      inverts* Typ1.
    + SCase "e_merge e1 v2".
      inverts* Typ2.
    + SCase "e_merge e1 e2".
      inverts* Typ2.
Qed.
