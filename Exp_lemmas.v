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

Lemma exp_lit_not_func : forall i T1 T2,
    not (typing empty (exp_lit i) (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))).
Proof.
  intros i T1 T2 H. remember (exp_lit i) as e_lit. inversion H; subst.
  - inversion H3.
  - inversion H2.
  - inversion H3.
  - inversion H3.
  - inversion H3.
  - eapply typ_inst in H1. (* apply (unique_typing_rho (exp_lit i) _ _ H4) in H1. *)

Admitted.




Theorem canonical_forms_fun: forall t T1 T2,
  typing empty t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2)))
    -> is_value_of_tm t 
    -> exists u, t = exp_abs u.
Proof with eauto.
  intros. assert (Htyp := H).
  remember (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) as T.
  remember empty as G.
  induction H; subst; try discriminate; try destruct H0.
  - eexists... 
  - apply IHtyping...
    destruct rho.
    admit. (* TODO: finish canonical forms for functions *)
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

(* Lemma empty_ctx_typing_closed: forall e T, *)
(*   typing empty e T -> fv_tm e [=] {}. *)
(* Proof with eauto. *)
(*   intros e T H. *)
(*   assert (Hlc: lc_tm e)... *)
(*   induction H; subst; simpl in *; try fsetdec. *)
(* Admitted. *)

Theorem progress : forall e T,
  typing empty e T ->
    is_value_of_tm e \/ exists e', step e e'.
Proof with eauto.
  intros e T H. assert (H0 := H).
  remember empty as G.
  induction H0; subst;
  try (left; constructor)...
  - right; destruct IHtyping1; destruct IHtyping2...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun t _ _ H0_ H0). }
      destruct Hlam; subst...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun t _ _ H0_ H0). }
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



(* Strengthened version of the weakening lemma 
 * Referenced Stlc.Lec2_sol from Metalib repo *)
Theorem typing_weakening_strengthened : forall (E F G : ctx) t T,
  typing (G ++ E) t T 
    -> uniq (G ++ F ++ E)
    -> typing (G ++ F ++ E) t T.
Proof.
  intros E F G t T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst; eauto.
  - (* exp_abs *) 
    apply typ_abs with (L := dom (G0 ++ F ++ E) \u L).
    intros x Frx.
    rewrite_env (([(x, ty_poly_rho (ty_rho_tau tau1))] ++ G0) ++ F ++ E).
    apply H0.
    + auto.
    + simpl_env. reflexivity.
    + simpl_env. apply uniq_push.
      * assumption.
      * auto.
  - (* exp_let *) 
    apply (typ_let (dom (G0 ++ F ++ E) \u L) _ u t rho sig).
    + auto.
    + intros x Frx.
      rewrite_env (([(x, sig)] ++ G0) ++ F ++ E).
      apply H1.
      * auto.
      * simpl_env. reflexivity.
      * simpl_env. apply uniq_push.
        -- assumption.
        -- auto.
Qed. 
 
(** Original statemnent of the weakening lemma *)
Theorem typing_weakening : forall (E F : ctx) t T,
  typing E t T -> 
  uniq (F ++ E) ->
  typing (F ++ E) t T.
Proof.
  intros E F t T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.

(** Substitution for variables: same variable *)
Lemma subst_eq_var : forall (x : var) u,
  subst_tm u x (exp_var_f x) = u.
Proof.
  intros x u.
  simpl.
  destruct eq_dec.
  - reflexivity.
  - destruct n. reflexivity.
Qed.

(** Substitution for variables: different variable *)
Lemma subst_neq_var : forall (x y : var) u,
  y <> x ->
  subst_tm u x (exp_var_f y) = exp_var_f y.
Proof.
  intros x y u.
  simpl.
  intro Hneq.
  destruct eq_dec.
  - destruct Hneq. assumption.
  - reflexivity.
Qed.

(** Substituting the same variable in an expression doesn't make a difference *)
Lemma subst_same : forall y e,
  subst_tm (exp_var_f y) y e = e.
Proof.
  induction e; simpl; intros; eauto.
  - (* exp_var_f *) destruct (x == y); subst; eauto.
  - (* exp_abs *) rewrite IHe. auto.
  - (* exp_app *) 
    rewrite IHe1. 
    rewrite IHe2. 
    reflexivity.
  - (* exp_typed_abs *)
    rewrite IHe. reflexivity.
  - (* exp_let *) 
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - (* exp_type_anno *)    
    rewrite IHe. reflexivity.
Qed. 


(** If a variable doesn't appear free in a term, 
    substituting for it has no effect. *)
Lemma subst_tm_fresh_eq : forall (x : var) e u,
  x `notin` fv_tm e ->
  subst_tm u x e = e.
Proof.
  intros x e u H.
  induction e; eauto; 
    try (simpl in *; f_equal; eauto).
  - (* exp_var_f *)
    unfold subst_tm.
    destruct (x0 == x).
    + (* x0 = x *) 
      subst. simpl fv_tm in H. fsetdec.
    + (* x0 <> x *)  
      reflexivity.
Qed.

(** Free variables are not introduced by substitution. *)
Lemma fv_tm_subst_tm_notin : forall x y u e,
  x `notin` fv_tm e ->
  x `notin` fv_tm u ->
  x `notin` fv_tm (subst_tm u y e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *; 
    try assumption.
  - (* exp_var_f *)
    destruct (x0 == y).
    + (* x0 = y *) assumption.
    + (* x0 <> y *) simpl. assumption.
  - (* exp_abs *) apply IHe. assumption.
  - (* exp_app *)
    destruct_notin.
    apply notin_union.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - (* exp_typed_abs *) apply IHe. assumption.
  - (* exp_let *) 
    destruct_notin.
    apply notin_union.
    apply IHe1. assumption.
    apply IHe2. assumption.
  - (* exp_type_anno *) 
    apply IHe. assumption.
Qed.

(* If [x] is a fresh variable, [x] continues to be fresh we substitute all occurrences of [x] in [e] with [u]. *)
Lemma subst_tm_fresh_same : forall u e x,
  x `notin` fv_tm e ->
  x `notin` fv_tm (subst_tm u x e).
Proof.
  intros.
  induction e; simpl in *; auto.
  - (* exp_var_f *) 
    destruct (x0 == x).
    + (* x0 = x *) subst. fsetdec.
    + (* x0 <> x *) simpl. assumption.
Qed.

(* If [x] is a fresh variable, 
   the free variables of [e] after substituting 
   all occurrences of [x] in [e] with [u] are the 
   same as the free variables of [e] pre-substitution. *)
Lemma fv_tm_subst_tm_fresh : forall u e x,
  x `notin` fv_tm e ->
  fv_tm (subst_tm u x e) [=] fv_tm e.
Proof.
  intros.
  induction e; simpl in *; auto; try fsetdec.
  - (* exp_var_f *) 
    destruct (x0 == x).
    + (* x0 = x *) subst. fsetdec.
    + (* x0 <> x *) simpl. fsetdec.
  - (* exp_abs *) 
    rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    destruct_notin. 
    assumption.
    destruct_notin.
    apply H.
  - (* exp_typed_abs *) 
    rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    destruct_notin. 
    assumption.
    destruct_notin.
    apply H.
Qed.




(** We can commute free & bound variable substitution. 
    Note: the name of this lemma was automatically generated by LNgen -- see [Exp_inf.v]. 
    
    This lemma is most often used with [t2] as some fresh variable. *)
Lemma subst_tm_open_tm_wrt_tm :
forall t3 t1 t2 x1,
  lc_tm t1 ->
  subst_tm t1 x1 (open_tm_wrt_tm t3 t2) = open_tm_wrt_tm (subst_tm t1 x1 t3) (subst_tm t1 x1 t2).
Proof.
   unfold open_tm_wrt_tm;
   default_simp.
   Admitted. (* TODO: not sure how to proceed *) 

(** Corollary of the above lemma for fresh variables. *)  
Lemma subst_var : forall (x y : var) u e,
  y <> x ->
  lc_tm u ->
  open_tm_wrt_tm (subst_tm u x e) (exp_var_f y) = 
    subst_tm u x (open_tm_wrt_tm e (exp_var_f y)).
Proof.
  intros x y u e Hneq Hlc.
  rewrite subst_tm_open_tm_wrt_tm; auto.
  rewrite subst_neq_var; auto.
Qed.

(* TODO: subst_exp_intro ??? *)



   
(* NB: In the Metalib notes, [[ z ~> u ] e] denotes[subst_exp u z e] *)  


(** Variable case of the substitution lemma *)
Lemma typing_subst_var_case : forall (E F : ctx) u S T (z x : atom),
  binds x T (F ++ [(z, S)] ++ E) ->
  uniq (F ++ [(z, S)] ++ E) -> 
  typing E u S ->
  typing (F ++ E) (subst_tm u z (exp_var_f x)) T.
Proof.
  intros E F u S T z x Hbinds Huniq Htyp.
  simpl.
  destruct eq_dec.
  - subst. assert (T = S).
    + (* T = S *)
      eapply binds_mid_eq.
      apply Hbinds.
      apply Huniq.
    + subst.
      apply typing_weakening.
      ++ assumption.
      ++ eapply uniq_remove_mid. apply Huniq.
  - apply typ_var.
    + eapply uniq_remove_mid. apply Huniq.
    + eapply binds_remove_mid.
      ++ apply Hbinds.
      ++ assumption.
Qed.

Lemma typing_to_lc_tm : forall E e T,
    typing E e T -> lc_tm e.
Proof.
  Admitted.

(** Substitution lemma *)      
Lemma typing_subst : forall (E F : ctx) e u S T (z : atom), 
  typing (F ++ [(z, S)] ++ E) e T ->
  typing E u S ->
  typing (F ++ E) (subst_tm u z e) T.
Proof.
  intros E F e u S T z He Hu.
  remember (F ++ [(z, S)] ++ E) as E'.
  generalize dependent F.
  induction He; subst; auto.
  - (* typ_int *) 
    intros F Heq.
    subst.
    simpl in *.
    apply typ_int.
  - (* typ_var *)     
    intros F Heq.
    subst.
    eapply typing_subst_var_case.
    apply H0.
    apply H.
    apply Hu.
  - (* typ_abs *) 
    intros F Heq.
    subst.
    simpl.
    apply typ_abs with (L := {{z}} \u L).
    intros y Fry.
    rewrite subst_var.
    rewrite_env (([(y, ty_poly_rho (ty_rho_tau tau1))] ++ F) ++ E).
    apply H0.
    auto.
    simpl_env. reflexivity.
    auto.
    eapply typing_to_lc_tm. apply Hu.
  - intros F Heq. simpl. eapply typ_app.
    ++ apply (IHHe1 _ Heq).
    ++ apply (IHHe2 _ Heq).
  - intros F Heq. eapply typ_let.
    ++ eauto.
    ++ Search subst_tm. admit.
  - simpl. admit.
  - intos F Heq.



    
Admitted.



Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.

Proof with eauto.
  intros E e e' T Htyp Hstep.


Admitted.

