Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

From Exp Require Export Exp_ott.

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
(* Notation "S -> T" := (Ty_Arrow S T) (in custom exp at level 50, right associativity) : exp_scope *)
Notation "x y" := (exp_app x y) (in custom exp at level 1, left associativity) : exp_scope.
Notation "\ x : t , y" :=
  (exp_abs x t y) (in custom exp at level 90, x at level 99,
                     t custom exp at level 99,
                     y custom exp at level 99,
                     left associativity) : exp_scope.

Local Open Scope exp_scope.                     

(* Variant of is_value_of_tm which is type Prop instead of bool *)
Definition is_value (t : tm) : Prop := 
  match t with 
  | exp_lit _ => True 
  | exp_abs _ => True 
  | exp_typed_abs _ _ => True 
  | _ => False 
  end.


(* Inductive value : tm -> Prop :=
  | v_int : forall (i : integer), 
      value <{ exp_lit i }>
  | v_abs : forall x T2 t1,
      value <{ \ x : T2 , t1 }>.
       *)




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




Theorem progress : forall e T,
  typing empty e T ->
  is_value e \/ exists e', step e e'.
Proof.
  intros e T H.
  assert (typing empty e T); auto.
  induction H; subst; auto.
  - (* exp_lit *)
   left. admit.
  - (* exp_lit duplicate *)
    admit.
  Admitted.
