Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.MetatheoryAtom.
Require Export Metalib.LibLNgen.

From Exp Require Export Exp_ott.
From Exp Require Export Exp_inf.

(*************************************************************************)
(** Notation, manually added *)
(*************************************************************************)

Notation "Gamma '|-' t '\in' T" := (typing Gamma t T) (at level 40).

(* Empty context is represented as an empty list *)
Definition empty : list (atom * ty_poly) := nil.

(* Int datatype in the object language *)
Definition Int : ty_poly := (ty_poly_rho (ty_rho_tau ty_mono_base)).

(** Tells Coq to create a new custom grammar Exp for parsing the object language *)
(** See Imp chapter of Software Foundations for details *)
(* Coercion exp_lit : integer >-> tm. *)

Declare Custom Entry exp.
Declare Scope exp_scope.


Notation "<{ e }>" := e (at level 0, e custom exp at level 99) : exp_scope.
Notation "( x )" := x (in custom exp, x at level 99) : exp_scope.
Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom exp at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : exp_scope.
(* Notation "'exp_lit' i" := (exp_lit i) (in custom exp at level 80) : exp_scope. *)


Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
(* Notation "S -> T" := (ty_mono_func S T) (in custom exp at level 50, right associativity) : exp_scope *)
Notation "x y" := (exp_app x y) (in custom exp at level 1, left associativity) : exp_scope.
Notation "\ x : t , y" :=
  (exp_abs x t y) (in custom exp at level 90, x at level 99,
                     t custom exp at level 99,
                     y custom exp at level 99,
                     left associativity) : exp_scope.

Local Open Scope exp_scope.                     



(*************************************************************************)
(** Lemmas, manually added *)
(*************************************************************************)

(* Note: this doesn't compile even when surrounding exp_lit with <{ }> *)
(* Lemma canonical_forms_int : forall (t : tm), 
  typing empty t Int ->
  is_value t ->
  exists (i : integer), t = <{ exp_lit i }>.
Proof.
  intros t HT HVal.
  destruct HVal. *)

Lemma exp_abs_not_base : forall (Gamma: ctx) (t : tm),
    not (typing Gamma (exp_abs t) Int).
Proof.
  intros Gamma t H. remember (exp_abs t) as t_fun. induction H; try (inversion Heqt_fun).
  - subst. simpl in *. pick fresh x0 for L. apply H0 in Fr; auto. admit.
  - pick fresh x0 for L. apply H0 in Fr; auto.
  - auto.
Admitted.

Lemma exp_typed_abs_not_base : forall Gamma (t : tm) T,
    not (typing Gamma (exp_typed_abs T t) Int).
Proof.
  intros Gamma t T H. remember (exp_typed_abs T t) as t_fun. induction H; try (inversion Heqt_fun).
  - pick fresh x0 for L. specialize H0 with x0. apply H0; auto.
  - auto.
Qed.
  

Lemma canonical_forms_int : forall (t : tm),
    typing empty t Int ->
    is_value_of_tm t ->
    exists (i : integer), t = exp_lit i.
Proof with eauto.
  intros. induction t; try (destruct H0).
  - exists i. reflexivity.
  - apply exp_abs_not_base in H. destruct H.
  - inversion H; subst. apply exp_typed_abs_not_base in H. inversion H.
Qed.

(* Is this actually correct? Shouldn't we open it wrt to some mono type? *)
Theorem typing_inversion_gen: forall G t T1,
  typing G t (ty_poly_poly_gen T1) ->
    typing G t T1.
Proof with eauto.
  intros. remember (ty_poly_poly_gen T1) as T2. induction H.
  - inversion HeqT2.
  - subst. induction T1.
    +  admit. (* Probably need to use the inst rule here... but how *)
    + 



  (* ; try (inversion HeqT2; subst). *)
  (* -  *)


  (* inversion H; subst. *)
  (* -  *)


    admit.
Admitted.

Theorem unique_typing_rho: forall G t T1 T2,
  typing G t (ty_poly_rho T1)
    -> typing G t (ty_poly_rho T2)
    -> T1 = T2.
Proof with eauto.
  intros G t T1 T2 H1 H2.
  destruct T1. destruct T2. f_equal.
  generalize dependent tau0.
  induction t; intros.
  - inversion H1; inversion H2; subst...
    +
Admitted.

Lemma exp_lit_not_func : forall Gamma i T1 T2,
    not (typing Gamma (exp_lit i) (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))).
Proof.
  intros Gamma i T1 T2 H. remember (exp_lit i) as e_lit. inversion H; subst. Admitted.


(*   remember (exp_typed_abs T t) as t_fun. induction H; try (inversion Heqt_fun). *)
(*   - pick fresh x0 for L. specialize H0 with x0. apply H0; auto. *)
(*   - auto. *)
(* Qed. *)

(* I think you can also have typed_abs in there?*)
Theorem canonical_forms_fun_mod: forall G t T1 T2,
  typing G t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))
    -> is_value_of_tm t 
    -> (exists u, t = exp_abs u) \/ (exists u sig, t = exp_typed_abs sig u).
Proof with eauto.
  intros. induction t; try (destruct H0).
  - inversion H; subst. admit.
  - left. exists t. reflexivity.
  - right. exists t. exists sig. auto.
Admitted.

Theorem canonical_forms_fun: forall G t T1 T2,
  typing G t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))
    -> is_value_of_tm t 
    -> (exists u, t = exp_abs u).
Proof with eauto.
  intros. induction t; try (destruct H0).
  - inversion H; subst. admit.
  - left. exists t. reflexivity.
  - right. exists t. exists sig.auto

  
  (* intros. induction t... *)
  (* - (* exp_lit i = exp_abs u *) *)
  (*   induction H... *)
  
Admitted.

Lemma empty_ctx_typing_lc: forall e T,
  typing empty e T -> lc_tm e.
Proof with eauto.
  intros e T H.
  induction H; subst...
  - destruct H...
  - destruct (atom_fresh L).
    apply (H0 x)...
Qed.

#[export] Hint Resolve empty_ctx_typing_lc : core.

Lemma empty_ctx_typing_closed: forall e T,
  typing empty e T -> fv_tm e [=] {}.
Proof with eauto.
  intros e T H.
  assert (Hlc: lc_tm e)...
  induction H; subst; simpl in *; try fsetdec.
Admitted.

Theorem progress : forall e T,
  typing empty e T ->
    is_value_of_tm e \/ exists e', step e e'.
Proof with eauto.
  intros e T H. assert (H0 := H).
  remember empty as G.
  induction H0; subst; auto;
  try (left; constructor)...
  - right; destruct IHtyping1; destruct IHtyping2...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun empty t _ _ H0_ H0). }
      destruct Hlam; subst...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun empty t _ _ H0_ H0). }
      destruct Hlam as [t1 Hlam]; subst...
      destruct H1 as [u' H1]. eexists...
    + destruct H0 as [t' H0]. eexists...
    + destruct H0 as [t' H0]. eexists...
  - right; destruct IHtyping...
    destruct H3 as [u' H3]. exists (exp_let u' t)...
  - right; destruct IHtyping...
    + destruct H0. eexists...
    + destruct H0. destruct H2 as [t' H2]. eexists...
  - destruct (atom_fresh L).
    specialize H0 with x; specialize H1 with x.
    assert (n1 := n); apply H0 in n; apply H1 in n1...
Qed.

Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.
Proof.
  intros E e e' T Htyp Hstep.
  Admitted.
