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

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => fv_tm x) in
  let D := gather_atoms_with (fun x => ftv_mono_ctx x) in
  let E := gather_atoms_with (fun x => ftv_mono_tm x) in
  let F := gather_atoms_with (fun x => ftv_mono_ty_mono x) in
  let G := gather_atoms_with (fun x => ftv_mono_ty_poly x) in
  let H := gather_atoms_with (fun x => ftv_mono_ty_rho x) in
  constr:(A \u B \u C \u D \u E \u F \u G).


(*************************************************************************)
(** Lemmas, manually added *)
(*************************************************************************)

(* Lemma gen_inst_int: forall tau sig x, *)
(*   inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau ty_mono_base)  *)
(*     -> inst sig (ty_rho_tau ty_mono_base). *)
(* Proof. *)
(*   intros tau sig x Hinst. dependent induction Hinst; intros. *)
(*   - destruct sig. *)
(*     + destruct rho. simpl in x. inversion x. clear x; simpl in H1. *)
(*     admit. *)
(*       (* destruct subst_ty_mono_ty_mono_fresh_eq in H1... *)
(*       destruct tau0; try discriminate. exists tau0_1. exists tau0_2. *)
(*       constructor. rewrite H1 in H... admit. *) *)
(*     + simpl in x. discriminate. *)
(*   - admit. *)
(*   Admitted. *)

(* Lemma canonical_forms_int : forall (t : tm) T, *)
(*     typing empty t T -> *)
(*     inst T (ty_rho_tau ty_mono_base) -> *)
(*     is_value_of_tm t -> *)
(*     exists (i : integer), t = exp_lit i. *)
(* Proof with eauto. *)
(*   intros t T Ht Hi Hv. generalize dependent Hi. *)
(*   dependent induction Ht; intros; try destruct Hv... *)
(*   - inversion Hi; subst. *)
(*   - pick fresh x. *)
(*     specialize (H x ltac:(auto)). specialize (H0 x ltac:(auto) ltac:(eauto) Hv). *)
(*     inversion Hi; subst. *)
(*     specialize H2 with x. *)
(*     rewrite (subst_ty_mono_ty_poly_intro x) in H2. *)
(*     apply (gen_inst_int _ _ x) in H2. *)
(*     apply (H0 H2). admit. fsetdec. *)
(*   - *)
(* Qed. *)

(* Lemma gen_inst_fun: forall tau sig T1 T2 x, *)
(*   inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau (ty_mono_func T1 T2))  *)
(*     -> (exists T1' T2', inst sig (ty_rho_tau (ty_mono_func T1' T2'))) \/ *)
(*         sig = ty_poly_rho (ty_rho_tau (ty_mono_var_f x)). *)
(* Proof with eauto. *)
(*   intros tau sig T1 T2 x Hinst. dependent induction Hinst; intros. *)
(*   - destruct sig. *)
(*     + destruct rho. simpl in x. inversion x. clear x; simpl in H1. *)
(*       rewrite subst_ty_mono_ty_mono_fresh_eq in H1... *)
(*       destruct tau0; try discriminate. left. exists tau0_1. exists tau0_2. *)
(*       constructor. rewrite H1 in H... *)
(*       induction tau0; simpl in H1; try discriminate. destruct (a == x0). *)
(*       ++ inversion H; subst. inversion H2; subst.  (* Don't know how to proceed *) admit. *)
(*       ++ discriminate. *)
(*       ++ simpl. *)
(*          Search union. injection H1; intros. admit. (* apply notin_union_3. *) constructor. rewrite *)


Lemma gen_inst_fun: forall tau sig T1 T2 x,
  inst (subst_ty_mono_ty_poly tau x sig) (ty_rho_tau (ty_mono_func T1 T2))
    -> exists T1' T2', inst sig (ty_rho_tau (ty_mono_func T1' T2')) .
Proof with eauto.
  intros tau sig T1 T2 x Hinst. dependent induction Hinst; intros.
  - destruct sig.
    + destruct rho. simpl in x. inversion x. clear x; simpl in H1.
      rewrite subst_ty_mono_ty_mono_fresh_eq in H1...
      destruct tau0; try discriminate. exists tau0_1. exists tau0_2.
      constructor. rewrite H1 in H...
      induction tau0; simpl in H1; try discriminate. destruct (a == x0).
      ++ destruct tau; try discriminate. injection H1; intros; subst. 
         inversion H; subst. inversion H2; subst.
         (* Don't know how to proceed *) admit.
      ++ discriminate.
      ++ Search union. apply notin_union_3.
         +++ apply IHtau0_1. simpl. injection H1; intros.  admit. (* apply notin_union_3. *)
         +++ admit.
    + simpl in x. discriminate.
  - destruct sig.
    + simpl in x. discriminate.
    + eexists. eexists. eapply inst_trans. 





      (* simpl in x. inversion x; subst. clear x. *)
      (* specialize (IHHinst tau (open_ty_poly_wrt_ty_mono sig tau0) T1 T2 x0). *)
      (* rewrite subst_ty_mono_ty_poly_open_ty_poly_wrt_ty_mono in IHHinst. *)
      (* rewrite subst_ty_mono_ty_mono_fresh_eq in IHHinst... *)
      (* specialize (IHHinst ltac:(eauto) ltac:(eauto)). *)
      (* rewrite ftv_mono_ty_poly_open_ty_poly_wrt_ty_mono_upper in IHHinst. *)
      
      admit.
Admitted.


(* Theorem canonical_forms_fun : forall t T1 T2, *)
(*     typing empty t (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) *)
(*     -> inst (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) (ty_rho_tau (ty_mono_func T1 T2)) *)
(*     -> is_value_of_tm t *)
(*     -> exists u, t = exp_abs u. *)
(* Proof with eauto. *)
(*   intros t T1 T2. remember (ty_poly_rho (ty_rho_tau (ty_mono_func T1 T2))) as T. *)
(*   induction t; intros; inversion H1. *)
(*   - rewrite HeqT in H. inversion H. inversion H6; subst. *)
(*     + induction sig. *)
(*       ++ unfold  *)

Fixpoint is_fun_mono τ :=
  match τ with
  | ty_mono_func _ _ => true
  | _ => false
  end.

Fixpoint is_fun_rho ρ :=
  match ρ with
  | ty_rho_tau τ => is_fun_mono τ
  end.

Fixpoint is_fun_poly ρ :=
  match ρ with
  | ty_poly_rho ρ' => is_fun_rho ρ'
  | ty_poly_poly_gen ρ' => is_fun_poly ρ'
  end.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Hammer Require Import Tactics.

Lemma is_fun_poly_open ρ τ :
  is_fun_poly ρ -> is_fun_poly (open_ty_poly_wrt_ty_mono ρ τ).
Proof.
  elim : ρ τ; sauto lq:on.
Qed.

(* Lemma open_preserves_fun_poly ρ τ : *)
(*   is_fun_poly (open_tm_wrt_tm ρ τ) = is_fun_poly ρ *)

Fixpoint bad_empty_mono τ :=
  match τ with
  | ty_mono_var_b _ => true
  | ty_mono_var_f _ => true
  | _ => false
  end.

Fixpoint bad_fun_rho ρ :=
  match ρ with
  | ty_rho_tau τ => bad_empty_mono τ
  end.

Fixpoint bad_fun_poly ρ :=
  match ρ with
  | ty_poly_rho ρ => bad_fun_rho ρ
  | ty_poly_poly_gen ρ => bad_fun_poly ρ
  end.

Theorem wt_implies_no_bad_poly Γ t ρ
  (h : typing Γ t ρ) :
  is_value_of_tm t ->
  ~~ bad_fun_poly ρ.
Proof.
  elim : Γ t ρ / h; try (by []).
  - move => *;
    pick fresh x; repeat (spec x);
    hauto q:on inv:ty_mono, ty_rho, ty_poly.
  - hauto q:on inv:ty_mono, ty_rho, ty_poly.
Qed.

Lemma bad_fun_poly_open : forall ρ τ,
  ~~ bad_fun_poly ρ ->
  is_fun_poly (open_ty_poly_wrt_ty_mono ρ τ) =
    is_fun_poly ρ.
  case; sauto lq:on.
Qed.

Theorem canonical_forms_fun: forall t ρ,
  typing empty t ρ
    -> is_fun_poly ρ
    -> is_value_of_tm t
    -> exists u, t = exp_abs u.
Proof with eauto.
  intros t T Ht.
  dependent induction Ht; subst; try discriminate; try by []; intros.
  - hauto lq:on.
  - pick fresh x; repeat (spec x).
    eapply_first_hyp; eauto.
    hauto lq:on use:is_fun_poly_open.
  - eapply_first_hyp; eauto.
    hauto q:on use:bad_fun_poly_open, wt_implies_no_bad_poly.
Qed.


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

Lemma empty_ctx_typing_lc_ty: forall e T,
  typing empty e T -> lc_ty_poly T.
Proof with eauto.
  intros e T H.
  dependent induction H; subst...
  - destruct H0...
  - pick fresh x. apply notin_union_1 in Fr as Fr0. specialize H0 with x. apply H0 in Fr0 as H1.
    + repeat constructor.
      ++ (* specialize H with x. apply H in Fr0 as H2. destruct tau1; try constructor. *)
        (* +++ simpl in H2. inversion H2. *) admit.
      ++ inversion H1; subst. inversion H3; subst. auto.
    + simpl. admit.
  - Search "~=". 





    admit.
Admitted.

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
  induction H0; subst;
  try (left; constructor)...
  - right; destruct IHtyping1; destruct IHtyping2...
    + assert (Hlam: exists u, t = exp_abs u) by
      sfirstorder use:canonical_forms_fun.
      { apply (canonical_forms_fun t _ H0_ tau1 tau2)... constructor.
        eapply empty_ctx_typing_lc_ty in H0_. inversion H0_... }
      destruct Hlam; subst...
    + assert (Hlam: exists u, t = exp_abs u).
      { apply (canonical_forms_fun t _ H0_ tau1 tau2)... constructor.
      eapply empty_ctx_typing_lc_ty in H0_. inversion H0_... }
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
  induction H; intros G0 Eq Uniq; subst; auto.
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
  - eauto.
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
  - eauto. Unshelve. apply L.
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

(* Opening can be replaced with variable opening & substitution *)
Lemma subst_tm_intro : forall (x : tmvar) u e,
  x `notin` (fv_tm e) ->
  open_tm_wrt_tm e u = subst_tm u x (open_tm_wrt_tm e (exp_var_f x)).
Proof.
  intros x u e FV_TM.
  unfold open_tm_wrt_tm.
  generalize 0.
  induction e; intro n0; simpl; eauto.
  - (* var_b *)
    destruct (lt_eq_lt_dec n n0).
    + destruct s. 
      * simpl. auto.
      * rewrite subst_eq_var. auto.
    + simpl. auto.
  - (* var_f *)
    destruct (x0 == x). subst.
    simpl in FV_TM. 
    fsetdec. auto.
  - (* abs *)
    f_equal.
    simpl in FV_TM.
    apply IHe.
    assumption.
  - (* app *)
    simpl in FV_TM.
    f_equal.
    + apply IHe1. auto.
    + apply IHe2. auto.
  - (* typed_abs *)    
    f_equal.
    simpl in FV_TM.
    apply IHe. 
    assumption.
  - (* let *)
    f_equal.
    simpl in FV_TM.
    + apply IHe1. fsetdec.
    + apply IHe2. simpl in FV_TM. fsetdec.
  - (* type_anno *)   
    f_equal.
    simpl in FV_TM.
    apply IHe.
    assumption.
Qed. 
    

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

(* Well-typed terms are locally closed. *)
Lemma typing_to_lc_tm : forall E e T,
    typing E e T -> lc_tm e.
Proof.
  intros E e T H.
  dependent induction H; eauto.
  - constructor.
    + auto.
    + destruct H. auto.
  - pick fresh x. apply H0 with x.
    apply notin_union_1 in Fr. auto.
Qed.

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
  - (* typ_app *)
    intros F Heq. simpl. eapply typ_app.
    ++ apply (IHHe1 _ Heq).
    ++ apply (IHHe2 _ Heq).
  - (* typ_let *)
    intros F Heq. eapply typ_let with (L := {{z}} \u L).  (* pick fresh x and apply typ_let. *) fold subst_tm.
    ++ eauto.
    ++ fold subst_tm. intros x Fry.
       rewrite subst_var.
       rewrite_env (([(x, sig)] ++ F) ++ E).
       apply H0.
       auto.
       subst. auto.
       auto.
       eapply typing_to_lc_tm. apply Hu.
  - (* exp_type_anno *)
    intros F Heq.
    eapply typ_annot; auto.
  - (* typ_gen *)
    intros F Heq.
    pick fresh x and apply typ_gen.
    apply H0; eauto.
Qed.


(* Simplified version of the substitution lemma *)
Lemma typing_subst_simple : forall (E : ctx) e u S T (z : atom),
  typing ([(z, S)] ++ E) e T ->
  typing E u S ->
  typing E (subst_tm u z e) T.
Proof.
  intros E e u S T z H J.
  rewrite_env (nil ++ E).
  eapply typing_subst.
  - simpl_env. apply H.
  - apply J.
Qed.


Theorem preservation : forall (E : ctx) e e' T,
  typing E e T
    -> step e e'
    -> typing E e' T.
Proof with eauto.
  intros E e e' T Htyp.
  generalize dependent e'.
  induction Htyp; intros e' J...
  - (* Literals don't step *) 
    inversion J.
  - (* Variables don't step *)
    inversion J.
  - (* Abs case *)
    inversion J.
  - (* App case *)
    inversion J; subst; eauto.
    + inversion Htyp1; subst.
      ++ pick fresh x. rewrite (subst_tm_intro x); auto. eapply typing_subst_simple; auto.
      ++ 


        pick fresh x. rewrite (subst_tm_intro x); auto. eapply typing_subst_simple; eauto. simpl.
         



         Print typing.
         admit.
    + 


      admit.
    (* inversion J; subst; eauto. *)
    (* + inversion Htyp1; subst. *)
    (*   * pick fresh y for (L \u fv_tm t0). *)
    (*     rewrite (subst_tm_intro y); auto. *)
    (*     eapply typing_subst_simple; auto. *)
    (*   * admit. *)
    (*     (* TODO: not sure how to prove typing derivations involving opening of terms *) *)
    (* + inversion Htyp1; subst. *)
    (*   admit. (* TODO: same problem as above *)  *)
  - (* Let case *)
    inversion J; subst; eauto.
    admit. (* TODO *)
  - (* typ_annot case -- this case is discharged *)
    inversion J; subst... 
Admitted.

