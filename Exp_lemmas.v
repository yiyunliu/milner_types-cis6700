Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
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

Theorem unique_typing: forall t T1 T2,
  typing empty t (ty_poly_rho T1)
    -> typing empty t (ty_poly_rho T2)
    -> T1 = T2.
Proof with eauto.
  intros t. induction t; intros.
  - inversion H; inversion H0; subst...
    + inversion H7.
    + 
Admitted.

Theorem canonical_forms_fun: forall G t T1 T2,
  typing G t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))
    -> is_value_of_tm t 
    -> exists u, t = exp_abs u.
Proof with eauto.
  intros. induction t...
  - (* exp_lit i = exp_abs u *)
    induction H...
  
Admitted.


Theorem progress : forall e T,
  typing empty e T ->
  is_value_of_tm e \/ exists e', step e e'.
Proof with eauto.
  intros e T H.
  (* We induct on the term e so that we always have a hypothesis 
    involving the empty context. *)
  induction e; subst; auto;
  try (left; constructor).
  - (* var shouldn't have a type in the empty context *)
    inversion H; subst...
    
Admitted.


Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.
Proof.
  intros E e e' T Htyp Hstep. 
