(****************************************************************

   File: ParRedR.v
   Authors: Amy Felty

   original: February 2014
   Apr 2021: Current Coq Version: V8.13.1

   Context relation version (R version) of:
   1. Substitution
   2. Attempt at Type Preservation for Parallel Reduction
   3. Adequacy

  ***************************************************************)

From HybridSys Require Export sl.

#[global] Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
#[global] Hint Resolve proper_APP abstr_proper : hybrid.
#[global] Hint Unfold proper: hybrid.

Section encoding.

(****************************************************************
   Types
  ****************************************************************)

Inductive tp: Set :=
   num : tp
 | arr : tp -> tp -> tp.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set := Cabs: Econ | Capp: Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (VAR Econ).
Definition lam : (uexp -> uexp) -> uexp :=
  fun f:uexp->uexp => (APP (CON Cabs) (lambda f)).
Definition app : uexp -> uexp -> uexp :=
  fun e1:uexp => fun e2:uexp => (APP (APP (CON Capp) e1) e2).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

Lemma proper_lam: forall (E:uexp -> uexp),
  abstr E -> proper (lam (fun x => E x)).
Proof.
unfold lam; auto with hybrid.
Qed.

Lemma proper_app: forall (E1 E2:uexp),
  proper E1 -> proper E2 -> proper (app E1 E2).
Proof.
unfold app; auto with hybrid.
Qed.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)
Inductive atm : Set :=
 | is_tm : uexp -> atm
 | oft : uexp -> tp -> atm
 | pr1 : uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  | tm_l : forall (M:uexp -> uexp),
      abstr M ->
      prog (is_tm (lam (fun x => (M x))))
        (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (M x))))))
  | tm_a : forall M N:uexp,
      prog (is_tm (app M N))
        (Conj (atom_ (is_tm M)) (atom_ (is_tm N)))
  | of_l :
      forall (A B: tp) (M: uexp -> uexp),
      abstr M ->
      prog (oft (lam (fun x => M x)) (arr A B))
        (All (fun x : uexp => Imp (oft x A) (atom_ (oft (M x) B))))
  | of_a :
      forall M N: uexp, forall A B : tp,
      prog (oft (app M N) A)
        (Conj (atom_ (oft M (arr B A))) (atom_ (oft N B)))
  | pr_l : forall (M N:uexp -> uexp),
      abstr M -> abstr N ->
      prog (pr1 (lam (fun x => (M x))) (lam (fun x => (N x))))
        (All (fun x : uexp => Imp (pr1 x x) (atom_ (pr1 (M x) (N x)))))
  | pr_b : 
      forall (M1 M2 : uexp -> uexp) (N1 N2:uexp),
      abstr M1 -> abstr M2 ->
      prog (pr1 (app (lam (fun x => M1 x)) N1) (M2 N2))
        (Conj
          (All (fun x : uexp => Imp (pr1 x x) (atom_ (pr1 (M1 x) (M2 x)))))
          (atom_ (pr1 N1 N2)))
  | pr_a :
      forall M1 M2 N1 N2: uexp,
      prog (pr1 (app M1 N1) (app M2 N2))
        (Conj (atom_ (pr1 M1 M2)) (atom_ (pr1 N1 N2))).

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := exists i : nat, seq_ i nil B.

End encoding.

#[global] Hint Resolve proper_Var : hybrid.
#[global] Hint Resolve tm_l tm_a of_l of_a pr_l pr_b pr_a : hybrid.
#[global] Hint Unfold oo_ atom_ T_: hybrid.
#[global] Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
  1. Substitution
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_subst.

Inductive xtG : list atm -> Prop :=
| nil_t : xtG nil 
| cons_t : forall (Phi_t:list atm) (x:uexp) (t:tp),
    proper x -> xtG Phi_t -> xtG (oft x t::Phi_t).

Hint Resolve nil_t cons_t : hybrid.

Lemma memb_xtG : forall (Phi_t:list atm) (E:uexp) (T:tp),
  xtG Phi_t -> In (oft E T) Phi_t -> proper E.
Proof.
intros Phi_t E T; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2]; try tauto.
injection h2; intros; subst; subst; simpl; auto.
Qed.

End ctx_subst.

(*********************)
(* "proper" Adequacy *)
(*********************)

#[global] Hint Resolve nil_t cons_t : hybrid.

Section proper_adeq.

Lemma oft_proper : forall (i:nat) (Phi_t:list atm) (E:uexp) (T:tp),
  xtG Phi_t ->
  seq_ i Phi_t (atom_ (oft E T)) -> proper E.
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (Phi_t:list atm) (E:uexp) (T:tp),
     xtG Phi_t ->
     seq_ i Phi_t (atom_ (oft E T)) -> proper E)).
intro h'.
apply h'; clear h'; auto.
clear i.
intros i h Phi_t E T cInv h1.
inversion h1; subst; clear h1.
- inversion H0; clear H0; subst; eauto with hybrid.
  + apply proper_lam; auto.
  + inversion H3; clear H3; subst.
    apply proper_app; auto.
    * apply h with i Phi_t (arr B T); auto; try lia.
    * apply h with i Phi_t B; auto; try lia.
- apply memb_xtG with (A'::L) T; auto.
Qed.

Lemma oft_proper_cor : forall (E:uexp) (T:tp),
  seq0 (atom_ (oft E T)) -> (proper E).
Proof.
intros E T [i h].
generalize (oft_proper i nil E T); intro h2.
apply h2; eauto with hybrid.
Qed.

End proper_adeq.

Section subst.

Theorem subst_oft :
  forall (i j:nat) (Phi_t:list atm) (M:uexp -> uexp) (N:uexp) (A B:tp),
  xtG Phi_t ->
  (forall x:uexp, proper x ->
    seq_ i (oft x A::Phi_t) (atom_ (oft (M x) B))) ->
  seq_ j Phi_t (atom_ (oft N A)) ->
  seq_ (i+j) Phi_t (atom_ (oft (M N) B)).
Proof.
intros i j Phi_t M N A B h1 h2 h3.
assert (h4:proper N).
{ apply oft_proper with j Phi_t A; auto. }
specialize h2 with (1:=h4).
apply seq_cut_aux with (oft N A); auto.
Qed.

End subst.

(****************************************************************
   2. Attempt at Type Preservation for Parallel Reduction
  ****************************************************************)

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Lemma oft_l_inv :
forall (i:nat) (Gamma:list atm) (T T':tp) (M:uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Gamma (Imp (oft x T) (atom_ (oft (M x) T')))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j ((oft x T)::Gamma) (atom_ (oft (M x) T'))).
Proof.
induction i; auto.
- intros Gamma T T' M H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros Gamma T T' M H.
  clear IHi.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

Lemma pr_l_inv :
forall (i:nat) (Gamma:list atm) (M N:uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Gamma (Imp (pr1 x x) (atom_ (pr1 (M x) (N x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j ((pr1 x x)::Gamma) (atom_ (pr1 (M x) (N x)))).
Proof.
induction i; auto.
- intros Gamma M N H.
  generalize (H (Var 0) (proper_Var 0)); intro H1.
  inversion H1; clear H1; subst.
  replace (i+1) with (S i) in H0; try lia.
- intros Gamma M N H.
  clear IHi.
  exists i; split; try lia.
  intros x H0.
  generalize (H x H0); intro H1.
  inversion H1; clear H1; subst.
  assert (i0 = i); try lia.
  subst; auto.
Qed.

(************)
(* Contexts *)
(************)

Section ctx_pr1.

Inductive xrtR : list atm -> list atm -> Prop :=
| xrt_nil : xrtR nil nil
| xrt_cons : forall (Phi_r Phi_t:list atm) (x:uexp) (t:tp), proper x ->
    xrtR Phi_r Phi_t -> xrtR (pr1 x x::Phi_r) (oft x t::Phi_t).

Lemma memb_type_pres : forall (Phi_r Phi_t:list atm) (M N:uexp),
  xrtR Phi_r Phi_t -> In (pr1 M N) Phi_r -> M=N.
Proof.
intros Phi_r Phi_t M N; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2]; auto.
injection h2; intros; subst; simpl; auto.
Qed.

Hint Resolve xrt_nil xrt_cons nil_t cons_t : hybrid.

Lemma xrtRxtG : forall (Phi_x Phi_t:list atm),
  xrtR Phi_x Phi_t -> xtG Phi_t.
Proof.
intros Phi_x Phi_t; induction 1; eauto with hybrid.
Qed.

End ctx_pr1.

#[global] Hint Resolve xrt_nil xrt_cons xrtRxtG : hybrid.

Section type_pres.

Lemma type_pres:
  forall (i j:nat) (Phi_r Phi_t:list atm) (M N:uexp) (A:tp),
  xrtR Phi_r Phi_t ->
  seq_ i Phi_r (atom_ (pr1 M N)) ->
  seq_ j Phi_t (atom_ (oft M A)) ->
  seq_ j Phi_t (atom_ (oft N A)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (j:nat) (Phi_r Phi_t:list atm) (M N:uexp) (A:tp),
     xrtR Phi_r Phi_t ->
     seq_ i Phi_r (atom_ (pr1 M N)) ->
     seq_ j Phi_t (atom_ (oft M A)) ->
     seq_ j Phi_t (atom_ (oft N A)))).
intro H'.
apply H'; clear H' i; auto.
intros i h j Phi_r Phi_t M N A cInv h1 h2.
inversion h1; subst; clear h1.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    inversion h2; subst; clear h2.
    * inversion H0; subst; clear H0.
      inversion H6; subst; clear H6.
      unfold seq_,atom_;
        apply s_bc with
            (All (fun x:uexp => (Imp (oft x A0) (atom_ (oft (N0 x) B)))));
        eauto with hybrid.
      apply s_all; auto.
      intros x h5.
      specialize H8 with (1:=h5); specialize H4 with (1:=h5).
      inversion H8; subst; clear H8.
      inversion H4; subst; clear H4.
      apply s_imp; auto.
      specialize abstr_lam_simp_eta with (1:=H7) (2:=H2) (3:=H); intro h1.
      rewrite -> h1 in H6; auto.
      clear h1 H H7 M.
      apply h with i1 (pr1 x x::Phi_r) (M0 x); try lia; eauto with hybrid.
    (* lam case: context subcase: can't be done *)
    *    
Abort.

End type_pres.

(****************************************************************
   3. Adequacy of oft
  ****************************************************************)

Section oft_adeq.

Inductive xtR : list atm -> list atm -> Prop :=
| xt_nil : xtR nil nil
| xt_cons : forall (Phi_x Phi_t:list atm) (x:uexp) (t:tp),
    proper x ->
    xtR Phi_x Phi_t ->
    xtR (is_tm x::Phi_x) (oft x t::Phi_t).

Hint Resolve xt_nil xt_cons : hybrid.

Lemma xtR_M : forall (Phi_x Phi_t:list atm) (M:uexp) (T:tp),
  xtR Phi_x Phi_t -> In (oft M T) Phi_t -> In (is_tm M) Phi_x.
Proof.
intros Phi_x Phi_t M T'; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
- injection h2; intros; subst; subst; simpl; auto.
- simpl; right; auto with hybrid.
Qed.

Hint Resolve xtR_M : hybrid.

Lemma oft_is_tm :
  forall (i:nat) (M:uexp) (T:tp) (Phi_x Phi_t:list atm),
  xtR Phi_x Phi_t ->
  seq_ i Phi_t (atom_ (oft M T)) ->
  seq_ i Phi_x (atom_ (is_tm M)).
Proof.
intro i.
generalize
 (lt_wf_ind i
   (fun i:nat =>
    forall (M : uexp) (T : tp) (Phi_x Phi_t : list atm),
    xtR Phi_x Phi_t ->
    seq_ i Phi_t (atom_ (oft M T)) -> seq_ i Phi_x (atom_ (is_tm M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M T Phi_x Phi_t h1 h2.
inversion h2; subst; clear h2.
- inversion H0; subst; clear H0.
  (* lam case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with
          (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (M0 x))))));
      auto with hybrid.
    apply s_all; auto.
    intros x h2.
    generalize (H2 x h2); clear H2; intro H2.
    inversion H2; subst; clear H2.
    apply s_imp; auto.
    apply h with B (oft x A::Phi_t); eauto with hybrid; try lia.
  (* app case *)
  + inversion H3; subst; clear H3.
    unfold seq_,atom_;
      apply s_bc with (Conj (atom_ (is_tm M0)) (atom_ (is_tm N)));
      auto with hybrid.
    apply s_and; auto.
    * apply h with (arr B T) Phi_t; auto; try lia.
    * apply h with B Phi_t; auto; try lia.
(* context case *)
- inversion h1; subst.
  apply s_init; eauto with hybrid.
Qed.

Lemma oft_is_tm_cor : forall (M:uexp) (T:tp),
  seq0 (atom_ (oft M T)) ->
  seq0 (atom_ (is_tm M)).
Proof.
intros M T [i h].
exists i.
generalize (oft_is_tm i M T nil nil); intro h2.
apply h2; eauto with hybrid.
Qed.

End oft_adeq.
