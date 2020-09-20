Require Import Metalib.Metatheory.
Add LoadPath "ours/" as La.
Add LoadPath "necolus/" as Ne.
From La Require Import LibTactics syntax_ott Infrastructure Type_Safety.
From Ne Require Import syntax_ott Infrastructure Source_Property Target_Safety.


Definition ltyp := La.syntax_ott.typ.
Definition lctx := La.syntax_ott.ctx.
Definition lexp := La.syntax_ott.exp.

Definition nctx := Ne.syntax_ott.ctx.
Definition nexp := Ne.syntax_ott.exp.
Definition ntyp := Ne.syntax_ott.typ.

Module la := La.syntax_ott.
Module ne := Ne.syntax_ott.


Fixpoint styp2ltyp (A:ne.styp) : la.typ :=
  match A with
    | styp_nat => t_int
    | styp_arrow A1 A2  => t_arrow (styp2ltyp A1) (styp2ltyp A2)
    | styp_and A1 A2 => t_and (styp2ltyp A1) (styp2ltyp A2)
    | styp_top => t_top
    | styp_rcd l A => t_rcd l (styp2ltyp A)
  end.

Definition sctx2lctx (C:ne.sctx) : la.ctx := map styp2ltyp C.


(* add elboration; add output type in lambdas *)
(* key: check mode & lambdas *)
Inductive has_type : sctx -> sexp -> ne.dirflag -> styp ->
                     ne.exp -> la.exp -> Prop :=    (* styping redefined *)
 | T_top : forall (GG:sctx),
      uniq  GG  ->
     has_type GG ne.e_top Inf styp_top trm_unit la.e_top
 | T_lit : forall (GG:sctx) (i5:i),
      uniq  GG  ->
     has_type GG (ne.e_lit i5) Inf styp_nat (trm_lit i5) (la.e_lit i5)
 | T_var : forall (GG:sctx) (x:var) (A:styp),
      uniq  GG  ->
      binds  x A GG  ->
     has_type GG (ne.e_var_f x) Inf A (trm_var_f x) (la.e_var_f x)
 | T_app : forall (GG:sctx) (ee1 ee2:sexp) (A2:styp) (e1 e2:ne.exp) (A1:styp) (t1 t2: la.exp),
     has_type GG ee1 Inf (styp_arrow A1 A2) e1 t1->
     has_type GG ee2 Chk A1 e2 t2->
     has_type GG (ne.e_app ee1 ee2) Inf A2 (trm_app e1 e2) (la.e_app t1 t2)
 | T_merge : forall (GG:sctx) (ee1 ee2:sexp) (A1 A2:styp) (e1 e2:ne.exp) (t1 t2: la.exp),
     has_type GG ee1 Inf A1 e1 t1 ->
     has_type GG ee2 Inf A2 e2 t2 ->
     ne.disjoint A1 A2 ->
     has_type GG (ne.e_merge ee1 ee2) Inf (styp_and A1 A2) (trm_pair e1 e2) (la.e_merge t1 t2)
 | T_rcd : forall (GG:sctx) (l:i) (ee:sexp) (A:styp) (e:ne.exp) (t: la.exp),
     has_type GG ee Inf A e t ->
     has_type GG (ne.e_rcd l ee) Inf (styp_rcd l A) (trm_rcd l e) (la.e_rcd l t)
 | T_proj : forall (GG:sctx) (ee:sexp) (l:i) (A:styp) (e:ne.exp) (t: la.exp),
     has_type GG ee Inf (styp_rcd l A) e t ->
     has_type GG (ne.e_proj ee l) Inf A (trm_proj e l) (la.e_proj t l)
 | T_anno : forall (GG:sctx) (ee:sexp) (A:styp) (e:ne.exp) (t: la.exp),
     has_type GG ee Chk A e t ->
     has_type GG (ne.e_anno ee A) Inf A e t
 | T_abs : forall (L:vars) (GG:sctx) (ee:sexp) (A B:styp) (e:ne.exp) (t: la.exp),
      ( forall x , x \notin  L  -> has_type  (( x ~ A )++ GG )   ( open_sexp_wrt_sexp ee (ne.e_var_f x) )  Chk B  ( ne.open_exp_wrt_exp e (trm_var_f x) )   ( la.open_exp_wrt_exp t (la.e_var_f x) ) )->
     has_type GG (ne.e_abs ee) Chk (styp_arrow A B) (trm_abs e) (la.e_abs (styp2ltyp A) t (styp2ltyp B))
 | T_sub : forall (GG:sctx) (ee:sexp) (A:styp) (c:co) (e:ne.exp) (B:styp) (t: la.exp),
     has_type GG ee Inf B e t->
     ne.sub B A c ->
     has_type GG ee Chk A (trm_capp c e) (la.e_anno t (styp2ltyp A)).

Hint Constructors has_type : core.

Lemma has_type_soundness : forall GG ee mode A e t,
    has_type GG ee mode A e t -> ne.has_type GG ee mode A e.
Proof.
  intros GG ee mode A e t H.
  induction* H.
Qed.

Lemma has_type_completeness : forall GG ee mode A e,
    ne.has_type GG ee mode A e -> exists t, has_type GG ee mode A e t.
Proof.
  intros GG ee mode A e H.
  induction H; jauto.
  - (* abs *)
    admit. (* close and rename *)
Qed.


Lemma dom_eq: forall x GG,
    x \notin dom GG -> x \notin dom (sctx2lctx GG).
Proof.
  intros x GG H.
  induction GG; simpl; eauto.
  destruct a.
  rewrite dom_cons in H.
  eauto.
Qed.

Lemma ctx_uniq: forall GG,
    uniq GG -> uniq (sctx2lctx GG).
Proof.
  intros GG H.
  induction H; simpl; eauto.
  constructor*. applys~ dom_eq.
Qed.

Lemma binds_ctx: forall x A GG,
    binds x A GG -> binds x (styp2ltyp A) (sctx2lctx GG).
Proof.
  intros x A GG H.
  induction~ GG.
  inverts H.
  - induction A; simpl; eauto.
  - destruct a.
    forwards*: IHGG.
    simpl.
    eapply binds_cons_3 in H.
    apply H.
Qed.

Hint Resolve ctx_uniq binds_ctx: core.

Lemma disjoint_completeness: forall A B,
    ne.disjoint A B -> la.disjoint (styp2ltyp A) (styp2ltyp B).
Proof.
  intros A B H.
  induction H; simpl; eauto.
Qed.

Lemma sub_completeness: forall A B c,
    ne.sub A B c -> la.sub (styp2ltyp A) (styp2ltyp B).
Proof.
  intros A B c H.
  induction H; simpl; eauto.
Qed.

(* source typing in necolus -> typing in our system *)
Theorem typing_completeness: forall (GG:sctx) ee mode A E t,
    has_type GG ee mode A E t -> Typing (sctx2lctx GG) t la.Inf (styp2ltyp A).
Proof.
  intros GG ee mode A E t H.
  induction~ H; simpl in *; eauto.
  - (* disjoint and*)
    apply disjoint_completeness in H1.
    eauto.
  - (* sub *)
    apply sub_completeness in H0.
    eauto.
Qed.


(* necolus target type to our types *)
Fixpoint ntyp2ltyp (A:ntyp) : ltyp :=
  match A with
  | a_nat => t_int
  | a_unit => t_top
  | a_arrow  A1 A2 => t_arrow (ntyp2ltyp A1) (ntyp2ltyp A2)
  | a_prod A1 A2 => t_and (ntyp2ltyp A1) (ntyp2ltyp A2)
  | a_rcd l A => t_rcd l (ntyp2ltyp A)
  end.

Lemma styp2ntyp2ltyp : forall A,
    ntyp2ltyp (ptyp2styp A) = styp2ltyp A.
Proof.
  intros A.
  induction* A; simpls; congruence.
Qed.


(* target typing for semantics relationship *)

(* necolus target typing *)
Inductive nettyping : nctx -> ne.exp -> ntyp -> la.exp -> Prop :=
 | ttyp_unit : forall (G:nctx),
      uniq  G  ->
     nettyping G trm_unit a_unit la.e_top
 | ttyp_lit : forall (G:nctx) (i5:i),
      uniq  G  ->
     nettyping G (trm_lit i5) a_nat (la.e_lit i5)
 | ttyp_var : forall (G:nctx) (x:var) (T:ntyp),
      uniq  G  ->
      binds  x T G  ->
     nettyping G (trm_var_f x) T (la.e_var_f x)
 | ttyp_abs : forall (L:vars) (G:nctx) (e:ne.exp) (T1 T2:ntyp) (t:la.exp),
      ( forall x , x \notin  L  -> nettyping  (( x ~ T1 )++ G )   ( ne.open_exp_wrt_exp e (trm_var_f x) )  T2 ( La.syntax_ott.open_exp_wrt_exp t (la.e_var_f x) ) )  ->
     nettyping G (trm_abs e) (a_arrow T1 T2) (la.e_abs (ntyp2ltyp T1) t (ntyp2ltyp T2) )
 | ttyp_app : forall (G:nctx) (e1 e2:ne.exp) (T2 T1:ntyp) (t1 t2:la.exp),
     nettyping G e1 (a_arrow T1 T2) t1 ->
     nettyping G e2 T1 t2 ->
     nettyping G (trm_app e1 e2) T2 (la.e_app t1 t2)
 | ttyp_pair : forall (G:nctx) (e1 e2:ne.exp) (T1 T2:ntyp) (t1 t2:la.exp),
     nettyping G e1 T1 t1 ->
     nettyping G e2 T2 t2 ->
     nettyping G (trm_pair e1 e2) (a_prod T1 T2) (la.e_merge t1 t2)
 | ttyp_capp : forall (G:nctx) (c:co) (e:ne.exp) (T' T:ntyp) (t:la.exp),
     nettyping G e T t ->
     cotyp c T T' ->
     nettyping G (trm_capp c e) T' (la.e_anno t (ntyp2ltyp T'))
 | ttyp_rcd : forall (G:nctx) (l:i) (e:ne.exp) (T:ntyp) (t:la.exp),
     nettyping G e T t ->
     nettyping G (trm_rcd l e) (a_rcd l T) (la.e_rcd l t)
 | ttyp_proj : forall (G:nctx) (e:ne.exp) (l:i) (T:ntyp) (t:la.exp),
     nettyping G e (a_rcd l T) t ->
     nettyping G (trm_proj e l) T (la.e_proj t l).

Hint Constructors nettyping : core.

Lemma nettyping_soundness : forall G e A t,
    nettyping G e A t -> ne.typing G e A.
Proof.
  intros G e A t H.
  induction* H.
Qed.

Lemma nettyping_completeness : forall G e A,
    ne.typing G e A -> exists t, nettyping G e A t.
Proof.
  intros G e A H.
  induction H; jauto.
  - (* abs *)
    admit. (* close and rename *)
Qed.

Lemma elaboration_sound: forall GG ee mode A e t,
    has_type GG ee mode A e t -> nettyping (map ptyp2styp GG) e (ptyp2styp A) t.
Proof.
  intros GG ee mode A e t H.
  induction H; simpls*; repeat rewrite <- styp2ntyp2ltyp; eauto.
  - (* co *)
    lets * : co_sound H0.
Qed.


Lemma step_typing: forall ee mode A E E' t t',
    has_type nil ee mode A E t
    -> nettyping nil E (ne.ptyp2styp A) t
    -> E ->* E'
    -> nettyping nil E' (ne.ptyp2styp A) t'
    -> Typing nil t la.Inf (styp2ltyp A) /\ Typing nil t' la.Inf (styp2ltyp A).
Abort.

(* may hold for some cases *)
(* excepetion: parallel reduction *)
Theorem step_completeness2: forall E E' A t t',
    nettyping nil E (ne.ptyp2styp A) t
    -> nettyping nil E' (ne.ptyp2styp A) t'
    -> ne.step E  E'
    -> la.step t  t'.
Abort.


Theorem step_completeness1: forall ee mode A E V t,
    has_type nil ee mode A E t
    -> E ->* V -> ne.value V
    -> exists t', nettyping nil V (ne.ptyp2styp A) t'
                  /\ (La.Infrastructure.star _ la.step) t  t'.
Proof.
  intros ee mode A E V t styp mstep val.
  (* lets vtyp: ne_preservation_multi_step ne_ttyp mstep. *)
  induction mstep.
  - (* value *)
    lets ne_ttyp : elaboration_sound styp.
    exists t. split*.
  - (* a b c *)
    exists t. split*.
    lets ne_ttyp : elaboration_sound styp.

    apply La.Infrastructure.star_refl.
    induction val; inverts styp.


  lets (u & utyp): nettyping_completeness vtyp.
  exists u. split~.
  lets~ : step_completeness_aux styp mstep utyp.
Qed.
