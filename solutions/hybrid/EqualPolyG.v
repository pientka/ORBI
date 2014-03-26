(****************************************************************

   File: EqualPolyG.v
   Author: Amy Felty
   Version: Coq V8.4pl2
   January 2014

   Generalized context version (G version) of:

   1. Admissibility of reflexivity of algorithmic equality for the
      polymorphically typed lambda calculus (types)
   2. Admissibility of reflexivity of algorithmic equality for the
      polymorphically typed lambda calculus (terms)
   3. Adequacy

  ***************************************************************)

Require Import sl.

Section encoding.

(****************************************************************
   Constants for Lambda Terms
  ****************************************************************)

Inductive Econ: Set :=
 Carr: Econ | Call: Econ | Capp: Econ | Clam: Econ |
 Ctapp: Econ | Ctlam: Econ.

Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (BND Econ).
Definition app : uexp -> uexp -> uexp :=
  fun M1:uexp => fun M2:uexp => (APP (APP (CON Capp) M1) M2).
Definition lam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON Clam) (lambda M)).
Definition tapp : uexp -> uexp -> uexp :=
  fun M:uexp => fun A:uexp => (APP (APP (CON Ctapp) M) A).
Definition tlam : (uexp -> uexp) -> uexp :=
  fun M:uexp->uexp => (APP (CON Ctlam) (lambda M)).
Definition arr : uexp -> uexp -> uexp :=
  fun A1:uexp => fun A2:uexp => (APP (APP (CON Carr) A1) A2).
Definition all : (uexp -> uexp) -> uexp :=
  fun A:uexp->uexp => (APP (CON Call) (lambda A)).

(****************************************************************
   Some Properties of Constructors
  ****************************************************************)

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.

Lemma proper_Var: forall x:var, (proper (Var x)).
Proof.
unfold Var; auto with hybrid.
Qed.

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)

Inductive atm : Set :=
 | is_tp : uexp -> atm
 | is_tm : uexp -> atm
 | atp : uexp -> uexp -> atm
 | aeq : uexp -> uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  (* well-formedness of types (arr and all) *)
  | tp_ar : forall A1 A2:uexp,
      prog (is_tp (arr A1 A2))
        (Conj (atom_ (is_tp A1)) (atom_ (is_tp A2)))
  | tp_al : forall A:uexp->uexp, abstr A ->
      prog (is_tp (all A))
        (All (fun a:uexp =>
          (Imp (is_tp a) (atom_ (is_tp (A a))))))
  (* well-formedness of terms (app, lam, tapp, tlam) *)
  | tm_a : forall M1 M2:uexp,
      prog (is_tm (app M1 M2))
        (Conj (atom_ (is_tm M1)) (atom_ (is_tm M2)))
  | tm_l : forall M:uexp->uexp, abstr M ->
      prog (is_tm (lam M))
        (All (fun x:uexp =>
          (Imp (is_tm x) (atom_ (is_tm (M x))))))
  | tm_ta : forall M A:uexp,
      prog (is_tm (tapp M A))
        (Conj (atom_ (is_tm M)) (atom_ (is_tp A)))
  | tm_tl : forall M:uexp->uexp, abstr M ->
      prog (is_tm (tlam M))
        (All (fun a:uexp =>
          (Imp (is_tp a) (atom_ (is_tm (M a))))))
  (* algorithmic equality for types *)
  | at_a : forall A1 A2 B1 B2:uexp,
      prog (atp (arr A1 A2) (arr B1 B2))
        (Conj (atom_ (atp A1 B1)) (atom_ (atp A2 B2)))
  | at_al : forall A B:uexp->uexp, abstr A -> abstr B ->
      prog (atp (all A) (all B))
        (All (fun a:uexp =>
          (Imp (atp a a) (atom_ (atp (A a) (B a))))))
  (* algorithmic equality for terms *)
  | ae_a : forall M1 M2 N1 N2:uexp,
      prog (aeq (app M1 M2) (app N1 N2))
        (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2)))
  | ae_l : forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (aeq (lam M) (lam N))
        (All (fun x:uexp =>
          (Imp (aeq x x) (atom_ (aeq (M x) (N x))))))
  | ae_ta : forall M N A B:uexp,
      prog (aeq (tapp M A) (tapp N B))
        (Conj (atom_ (aeq M N)) (atom_ (atp A B)))
  | ae_tl : forall M N:uexp->uexp, abstr M -> abstr N ->
      prog (aeq (tlam M) (tlam N))
        (All (fun a:uexp =>
          (Imp (atp a a) (atom_ (aeq (M a) (N a)))))).

Hint Resolve tp_ar tp_al tm_a tm_l tm_ta tm_tl
             at_a at_al ae_a ae_l ae_ta ae_tl : hybrid.

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := seq'_ nil B.

Hint Unfold seq_ seq'_ seq0: hybrid.

End encoding.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Resolve proper_Var : hybrid.
Hint Resolve tp_ar tp_al tm_a tm_l tm_ta tm_tl
             at_a at_al ae_a ae_l ae_ta ae_tl : hybrid.
Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Admissibility of Reflexivity for Types
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_tp.

(* Context Relation for reflexivity of types *)
Inductive atpG : list atm -> Prop :=
| nil_atp : atpG nil
| cons_atp : forall (Gamma:list atm) (a:uexp), proper a ->
    atpG Gamma -> atpG (is_tp a::atp a a::Gamma).

(* Context Membership *)
Lemma memb_refl_tp : forall (Gamma:list atm) (T:uexp),
  atpG Gamma -> (In (is_tp T) Gamma -> In (atp T T) Gamma).
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]].
injection h; intros; subst; simpl; auto.
discriminate.
simpl; tauto.
Qed.

Lemma atp_strengthen_weaken :
  forall (i:nat) (T T':uexp) (Phi Psi:list atm),
  (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
  seq_ i Phi (atom_ (atp T T')) ->
  seq_ i Psi (atom_ (atp T T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi Psi:list atm),
     (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
     seq_ i Phi (atom_ (atp T T')) ->
     seq_ i Psi (atom_ (atp T T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi Psi h1 h2.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
(* arr case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (atp A1 B1)) (atom_ (atp A2 B2)));
  auto with hybrid.
apply s_and; auto.
(* all case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (atp a a) (atom_ (atp (A a) (B a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
generalize (H4 a h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (atp a a::Phi); auto; try omega.
(* proof of extended context inv *)
intros T T'; generalize (h1 T T'); simpl; tauto.
(* context case *)
destruct (h1 T T') as [h2 h3].
generalize (h2 H2); clear h1 h2 h3 H2.
case Psi.
simpl; tauto.
intros a Phi h1.
apply s_init; auto with hybrid.
Qed.

Lemma d_str_alphatp2atp_atp :
  forall (i:nat) (T T' a:uexp) (Gamma:list atm),
  seq_ i (is_tp a::atp a a::Gamma) (atom_ (atp T T')) ->
  seq_ i (atp a a::Gamma) (atom_ (atp T T')).
Proof.
intros i T T' a Gamma h.
apply atp_strengthen_weaken with (is_tp a::atp a a::Gamma); auto.
clear h T T' i.
intros T T'; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

End ctx_tp.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section refl_tp.

Hint Resolve nil_atp cons_atp memb_refl_tp : hybrid.

Lemma atp_refl :
  forall (i:nat) (T:uexp) (Gamma:list atm),
  atpG Gamma ->
  seq_ i Gamma (atom_ (is_tp T)) ->
  seq_ i Gamma (atom_ (atp T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Gamma:list atm),
     atpG Gamma ->
     seq_ i Gamma (atom_ (is_tp T)) ->
     seq_ i Gamma (atom_ (atp T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Gamma cInv h1.
inversion h1; subst; clear h1.
inversion H0; subst; clear H0.
(* arr case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
specialize h' with (1:=hi) (2:=cInv) (3:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (atp A1 A1)) (atom_ (atp A2 A2)));
  auto with hybrid.
apply s_and; auto.
(* all case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (atp a a) (atom_ (atp (A a) (A a))))));
  auto with hybrid.
apply s_all; auto.
intros a h1.
generalize (H4 a h1); intro h2.
inversion h2; subst; clear h2.
apply s_imp; auto.
apply d_str_alphatp2atp_atp; auto.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (is_tp a::Gamma); auto.
intro a1; simpl; tauto.
(* context case *)
inversion cInv; subst.
apply s_init; eauto with hybrid.
Qed.

Lemma atp_refl_cor :
  forall (T:uexp), seq0 (atom_ (is_tp T)) -> seq0 (atom_ (atp T T)).
Proof.
intros T [n h].
generalize nil_atp; intro h1.
specialize atp_refl with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End refl_tp.

(****************************************************************
 2. Admissibility of Reflexivity for Terms
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_term.

(* Context Relation for reflexivity of terms *)
Inductive aeqG : list atm -> Prop :=
| nil_aeq : aeqG nil
| tcons_aeq : forall (Gamma:list atm) (a:uexp), proper a ->
    aeqG Gamma -> aeqG (is_tp a::atp a a::Gamma)
| acons_aeq : forall (Gamma:list atm) (x:uexp), proper x ->
    aeqG Gamma -> aeqG (is_tm x::aeq x x::Gamma).

(* Context Membership *)
Lemma memb_refl_term_atp : forall (Gamma:list atm) (T:uexp),
  aeqG Gamma -> (In (is_tp T) Gamma -> In (atp T T) Gamma).
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
injection h; intros; subst; simpl; auto.
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
Qed.

Lemma memb_refl_term_aeq : forall (Gamma:list atm) (T:uexp),
  aeqG Gamma -> (In (is_tm T) Gamma -> In (aeq T T) Gamma).
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
injection h; intros; subst; simpl; auto.
Qed.

Lemma aeq_strengthen_weaken :
  forall (i:nat) (T T':uexp) (Phi Psi:list atm),
  (forall (T T':uexp), In (aeq T T') Phi <->  In (aeq T T') Psi) ->
  (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
  seq_ i Phi (atom_ (aeq T T')) ->
  seq_ i Psi (atom_ (aeq T T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Phi Psi:list atm),
     (forall (T T':uexp), In (aeq T T') Phi <->  In (aeq T T') Psi) ->
     (forall (T T':uexp), In (atp T T') Phi <->  In (atp T T') Psi) ->
     seq_ i Phi (atom_ (aeq T T')) ->
     seq_ i Psi (atom_ (aeq T T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Phi Psi h1 h1' h2.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
(* app case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=h1') (4:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=h1') (4:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (aeq M1 N1)) (atom_ (aeq M2 N2)));
  auto with hybrid.
apply s_and; auto.
(* lam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M x) (N x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
generalize (H4 x h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (aeq x x::Phi); auto; try omega.
(* proof of extended context inv *)
intros T T'; generalize (h1 T T'); simpl; tauto.
intros T T'; generalize (h1 T T'); generalize (h1' T T'); simpl; tauto.
(* tapp case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=h1') (4:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=h1') (4:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (aeq M N)) (atom_ (atp A B)));
  auto with hybrid.
apply s_and; auto.
apply atp_strengthen_weaken with Phi; auto.
(* tlam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (atp a a) (atom_ (aeq (M a) (N a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
generalize (H4 a h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (atp a a::Phi); auto; try omega.
(* proof of extended context inv *)
intros T T'; generalize (h1 T T'); simpl; tauto.
intros T T'; generalize (h1 T T'); generalize (h1' T T'); simpl; tauto.
(* context case *)
destruct (h1 T T') as [h2 h3].
generalize (h2 H2); clear h1 h2 h3 H2.
case Psi.
simpl; tauto.
intros a Phi h1.
apply s_init; auto with hybrid.
Qed.

Lemma d_str_xa2a_aeq :
  forall (i:nat) (T T' x:uexp) (Gamma:list atm),
  seq_ i (is_tm x::aeq x x::Gamma) (atom_ (aeq T T')) ->
  seq_ i (aeq x x::Gamma) (atom_ (aeq T T')).
Proof.
intros i T T' x Gamma h.
apply aeq_strengthen_weaken with (is_tm x::aeq x x::Gamma); auto.
clear h T T' i.
intros T T'; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
clear h T T' i.
intros T T'; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

Lemma d_str_alphatp2atp_aeq :
  forall (i:nat) (T T' x:uexp) (Gamma:list atm),
  seq_ i (is_tp x::atp x x::Gamma) (atom_ (aeq T T')) ->
  seq_ i (atp x x::Gamma) (atom_ (aeq T T')).
Proof.
intros i T T' x Gamma h.
apply aeq_strengthen_weaken with (is_tp x::atp x x::Gamma); auto.
clear h T T' i.
intros T T'; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
clear h T T' i.
intros T T'; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

Lemma tp_strengthen_weaken :
  forall (i:nat) (T:uexp) (Phi Psi:list atm),
  (forall (T:uexp), In (is_tp T) Phi <->  In (is_tp T) Psi) ->
  seq_ i Phi (atom_ (is_tp T)) ->
  seq_ i Psi (atom_ (is_tp T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi Psi:list atm),
     (forall (T:uexp), In (is_tp T) Phi <->  In (is_tp T) Psi) ->
     seq_ i Phi (atom_ (is_tp T)) ->
     seq_ i Psi (atom_ (is_tp T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi Psi h1 h2.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
(* arr case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tp A1)) (atom_ (is_tp A2)));
  auto with hybrid.
apply s_and; auto.
(* all case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tp x) (atom_ (is_tp (A x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
generalize (H4 x h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (is_tp x::Phi); auto; try omega.
(* proof of extended context inv *)
intro T; generalize (h1 T); simpl; tauto.
(* context case *)
destruct (h1 T) as [h2 h3].
generalize (h2 H2); clear h1 h2 h3 H2.
case Psi.
simpl; tauto.
intros a Phi h1.
apply s_init; auto with hybrid.
Qed.

End ctx_term.

(*************)
(* Promotion *)
(*************)

Section promote.

Fixpoint rm_aeq2atp (l:list atm) {struct l} : list atm
  := match l with
     | (is_tp x::atp y z::l') =>
            (is_tp x::atp y z::rm_aeq2atp l')
     | (is_tm x::aeq y z::l') => (rm_aeq2atp l')
     | _ => nil
     end.

(* This version works as well:
Fixpoint rm_aeq2atp (l:list atm) {struct l} : list atm
  := match l with
       nil => nil
     | (is_tp x::l') => (is_tp x::rm_aeq2atp l')
     | (is_tm x::l') => (rm_aeq2atp l')
     | (atp x y::l') => (atp x y::rm_aeq2atp l')
     | (aeq x y::l') => (rm_aeq2atp l')
     end. *)

Hint Resolve nil_atp cons_atp : hybrid.
Hint Resolve nil_aeq tcons_aeq acons_aeq : hybrid.

(* Schema Strengthening *)
Lemma aeqG2atpG_strengthen : forall (Gamma:list atm),
  aeqG Gamma -> atpG (rm_aeq2atp Gamma).
Proof.
intros Gamma; induction 1; simpl; eauto with hybrid.
Qed.

Lemma rm_aeq2atp_lem_tp :
  forall (T:uexp) (Gamma:list atm),
  aeqG Gamma ->
  (In (is_tp T) Gamma <-> In (is_tp T) (rm_aeq2atp Gamma)).
Proof.
intros T Gamma; induction 1; try (simpl; tauto).
split; try (simpl; tauto).
simpl; intros [h1 | [h1 | h1]]; try tauto; try discriminate.
Qed.

Hint Resolve rm_aeq2atp_lem_tp : hybrid.

Lemma c_str_aeq2atp_tp :
  forall (i:nat) (T:uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (is_tp T)) ->
  seq_ i (rm_aeq2atp Gamma) (atom_ (is_tp T)).
Proof.
intros i T Gamma h1 h2.
apply tp_strengthen_weaken with Gamma;
  eauto with hybrid.
Qed.

Lemma rm_aeq2atp_lem_atp :
  forall (T T':uexp) (Gamma:list atm),
  aeqG Gamma ->
  (In (atp T T') (rm_aeq2atp Gamma) <-> In (atp T T') Gamma).
Proof.
intros T T' Gamma; induction 1; try (simpl; tauto).
split; try (simpl; tauto).
simpl; intros [h1 | [h1 | h1]]; try tauto; try discriminate.
Qed.

Hint Resolve rm_aeq2atp_lem_atp : hybrid.

Lemma c_wk_aeq2atp_atp :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i (rm_aeq2atp Gamma) (atom_ (atp T T')) ->
  seq_ i Gamma (atom_ (atp T T')).
Proof.
intros i T T' Gamma h1 h2.
apply atp_strengthen_weaken with (rm_aeq2atp Gamma);
  eauto with hybrid.
Qed.

Hint Resolve c_wk_aeq2atp_atp c_str_aeq2atp_tp aeqG2atpG_strengthen : hybrid.
Hint Resolve atp_refl : hybrid.

(* Promotion Lemma for Reflexivity of Types *)
Lemma afp_refl_promote :
  forall (i:nat) (A:uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (is_tp A)) ->
  seq_ i Gamma (atom_ (atp A A)).
Proof.
intros i A Gamma h h2; eauto with hybrid.
(* apply c_wk_aeq2atp_atp; auto.
   apply atp_refl; auto.
   apply aeqG2atpG_strengthen; auto.
   apply c_str_aeq2atp_tp; auto. *)
Qed.

End promote.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section refl_term.

Hint Resolve nil_aeq tcons_aeq acons_aeq : hybrid.
Hint Resolve memb_refl_term_atp memb_refl_term_aeq : hybrid.

Lemma aeq_refl :
  forall (i:nat) (T:uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (is_tm T)) ->
  seq_ i Gamma (atom_ (aeq T T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Gamma:list atm),
     aeqG Gamma ->
     seq_ i Gamma (atom_ (is_tm T)) ->
     seq_ i Gamma (atom_ (aeq T T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Gamma cInv h1.
inversion h1; subst; clear h1.
inversion H0; subst; clear H0.
(* app case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
specialize h' with (1:=hi) (2:=cInv) (3:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (aeq M1 M1)) (atom_ (aeq M2 M2)));
  auto with hybrid.
apply s_and; auto.
(* all case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (aeq x x) (atom_ (aeq (M x) (M x))))));
  auto with hybrid.
apply s_all; auto.
intros x h1.
generalize (H4 x h1); intro h2.
inversion h2; subst; clear h2.
apply s_imp; auto.
apply d_str_xa2a_aeq; auto.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (is_tm x::Gamma); auto.
intro a; simpl; tauto.
(* tapp case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (aeq M M)) (atom_ (atp A A)));
  auto with hybrid.
apply s_and; auto.
apply afp_refl_promote; auto.
(* tlam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (atp a a) (atom_ (aeq (M a) (M a))))));
  auto with hybrid.
apply s_all; auto.
intros a h1.
generalize (H4 a h1); intro h2.
inversion h2; subst; clear h2.
apply s_imp; auto.
apply d_str_alphatp2atp_aeq; auto.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (is_tp a::Gamma); auto.
intro a1; simpl; tauto.
(* context case *)
inversion cInv; subst.
apply s_init; eauto with hybrid.
apply s_init; eauto with hybrid.
Qed.

Lemma aeq_refl_cor :
  forall (T:uexp), seq0 (atom_ (is_tm T)) -> seq0 (atom_ (aeq T T)).
Proof.
intros T [n h].
generalize nil_aeq; intro h1.
specialize aeq_refl with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End refl_term.

(****************************************************************
 3. Adequacy
  ****************************************************************)

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section atp_inv.

Lemma at_al_inv :
forall (i:nat) (Phi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (atp x x) (atom_ (atp (T x) (T' x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (atp x x::Phi) (atom_ (atp (T x) (T' x)))).
Proof.
induction i; auto.
intros Phi T T' H.
generalize (H (Var 0) (proper_Var 0)); intro H1.
inversion H1; clear H1; subst.
replace (i+1) with (S i) in H0; try omega.
intros Phi T T' H.
exists i; split; try omega.
intros x H0.
generalize (H x H0); intro H1.
inversion H1; clear H1; subst.
assert (i0 = i); try omega.
subst; auto.
Qed.

End atp_inv.

(************)
(* Contexts *)
(************)

Section ctx_atp_adeq.

(* Membership lemma used in adequacy of atp *)
Lemma memb_atp_adeq1 : forall (Gamma:list atm) (T T':uexp),
  atpG Gamma -> In (atp T T') Gamma -> In (is_tp T) Gamma.
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
injection h; intros; subst; subst; simpl; auto.
Qed.

Lemma memb_atp_adeq2 : forall (Gamma:list atm) (T T':uexp),
  atpG Gamma -> In (atp T T') Gamma -> In (is_tp T') Gamma.
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; auto).
injection h; intros; subst; subst; simpl; auto.
Qed.

Lemma term_strengthen_weaken :
  forall (i:nat) (T:uexp) (Phi Psi:list atm),
  (forall (T:uexp), In (is_tm T) Phi <->  In (is_tm T) Psi) ->
  (forall (T:uexp), In (is_tp T) Phi <->  In (is_tp T) Psi) ->
  seq_ i Phi (atom_ (is_tm T)) ->
  seq_ i Psi (atom_ (is_tm T)).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T:uexp) (Phi Psi:list atm),
     (forall (T:uexp), In (is_tm T) Phi <->  In (is_tm T) Psi) ->
     (forall (T:uexp), In (is_tp T) Phi <->  In (is_tp T) Psi) ->
     seq_ i Phi (atom_ (is_tm T)) ->
     seq_ i Psi (atom_ (is_tm T)))).
intro H'.
apply H'; clear H' i; auto.
intros i h T Phi Psi h1 h1' h2.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
(* app case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=h1') (4:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=h1') (4:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm M1)) (atom_ (is_tm M2)));
  auto with hybrid.
apply s_and; auto.
(* lam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (M x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
generalize (H4 x h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (is_tm x::Phi); auto; try omega.
(* proof of extended context inv *)
intro T; generalize (h1 T); simpl; tauto.
intro T; generalize (h1 T); generalize (h1' T); simpl; tauto.
(* tapp case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=h1) (3:=h1') (4:=H4).
specialize h' with (1:=hi) (2:=h1) (3:=h1') (4:=H5).
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm M)) (atom_ (is_tp A)));
  auto with hybrid.
apply s_and; auto.
apply tp_strengthen_weaken with Phi; auto.
(* tlam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tp x) (atom_ (is_tm (M x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
generalize (H4 x h5); intro h6.
inversion h6; subst; clear h6 H4.
apply s_imp; auto.
apply h with (is_tp x::Phi); auto; try omega.
(* proof of extended context inv *)
intro T; generalize (h1 T); simpl; tauto.
intro T; generalize (h1 T); generalize (h1' T); simpl; tauto.
(* context case *)
destruct (h1 T) as [h2 h3].
generalize (h2 H2); clear h1 h2 h3 H2.
case Psi.
simpl; tauto.
intros a Phi h1.
apply s_init; auto with hybrid.
Qed.

Lemma d_str_alphatp2alph_tp :
  forall (i:nat) (T T' a:uexp) (Gamma:list atm),
  seq_ i (is_tp a::atp a a::Gamma) (atom_ (is_tp T)) ->
  seq_ i (is_tp a::Gamma) (atom_ (is_tp T)).
Proof.
intros i T T' a Gamma h.
apply tp_strengthen_weaken with (is_tp a::atp a a::Gamma); auto.
clear h T T' i.
intro T; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

End ctx_atp_adeq.

(****************)
(* atp Adequacy *)
(****************)

Section atp_adeq.

Hint Resolve nil_atp cons_atp memb_atp_adeq1 memb_atp_adeq2 : hybrid.

Lemma atp_tp :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  atpG Gamma ->
  seq_ i Gamma (atom_ (atp T T')) ->
  seq_ i Gamma (atom_ (is_tp T)) /\ seq_ i Gamma (atom_ (is_tp T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Gamma:list atm),
     atpG Gamma ->
     seq_ i Gamma (atom_ (atp T T')) ->
     seq_ i Gamma (atom_ (is_tp T)) /\ seq_ i Gamma (atom_ (is_tp T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Gamma cInv h1.
inversion h1; subst; clear h1.
inversion H0; subst; clear H0.
(* arr case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
specialize h' with (1:=hi) (2:=cInv) (3:=H5).
elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
split.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tp A1)) (atom_ (is_tp A2)));
  auto with hybrid.
apply s_and; auto.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tp B1)) (atom_ (is_tp B2)));
  auto with hybrid.
apply s_and; auto.
(* all case *)
inversion H3; subst; clear H3.
generalize (at_al_inv i Gamma A B H4); clear H4; intros [j [h1 h2]];
 subst.
assert (h':forall a:uexp, proper a -> 
        (seq_ j (is_tp a::atp a a::Gamma) (atom_ (is_tp (A a))) /\
         seq_ j (is_tp a::atp a a::Gamma) (atom_ (is_tp (B a))))).
intros a h1.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (atp a a::Gamma); simpl; auto.
apply h2; auto.
split.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (is_tp a) (atom_ (is_tp (A a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
apply s_imp; auto.
apply d_str_alphatp2alph_tp; auto.
generalize (h' a h5); tauto.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (is_tp a) (atom_ (is_tp (B a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
apply s_imp; auto.
apply d_str_alphatp2alph_tp; auto.
generalize (h' a h5); tauto.
(* context case *)
inversion cInv; subst.
split; apply s_init; eauto with hybrid.
Qed.

Lemma atp_tp1 :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  atpG Gamma ->
  seq_ i Gamma (atom_ (atp T T')) ->
  seq_ i Gamma (atom_ (is_tp T)).
Proof.
apply atp_tp.
Qed.

Lemma atp_tp2 :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  atpG Gamma ->
  seq_ i Gamma (atom_ (atp T T')) ->
  seq_ i Gamma (atom_ (is_tp T')).
Proof.
apply atp_tp.
Qed.

Lemma atp_tp_cor : forall T T':uexp, seq0 (atom_ (atp T T')) ->
  (seq0 (atom_ (is_tp T)) /\ seq0 (atom_ (is_tp T'))).
Proof.
intros T T' [n h].
generalize nil_atp; intro h1.
specialize atp_tp with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End atp_adeq.

(*************)
(* Promotion *)
(*************)

Section promote_atp_adeq.

Lemma c_str_aeq2atp_atp :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (atp T T')) ->
  seq_ i (rm_aeq2atp Gamma) (atom_ (atp T T')).
Proof.
intros i T T' Gamma h1 h2.
apply atp_strengthen_weaken with Gamma; eauto with hybrid.
intros T1 T2; rewrite <- rm_aeq2atp_lem_atp; eauto with hybrid; tauto.
(* "Hint Resolve rm_aeq2atp_lem_atp" would work except that <-> is
     in the wrong direction *)
Qed.

Lemma c_wk_aeq2atp_tp :
  forall (i:nat) (T:uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i (rm_aeq2atp Gamma) (atom_ (is_tp T)) ->
  seq_ i Gamma (atom_ (is_tp T)).
Proof.
intros i T Gamma h1 h2.
apply tp_strengthen_weaken with (rm_aeq2atp Gamma); eauto with hybrid.
intro T'; rewrite <- rm_aeq2atp_lem_tp; eauto with hybrid; tauto.
(* "Hint Resolve rm_aeq2atp_lem_tp" would work except that <-> is
     in the wrong direction *)
Qed.

Hint Resolve c_wk_aeq2atp_tp c_str_aeq2atp_atp aeqG2atpG_strengthen : hybrid.
Hint Resolve atp_tp1 atp_tp2 : hybrid.

(* Promotion Lemma for Adequacy of atp *)
Lemma atp_tp_promote :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (atp T T')) ->
  seq_ i Gamma (atom_ (is_tp T)) /\ seq_ i Gamma (atom_ (is_tp T')).
Proof.
intros i T T' Gamma h h2; split; eauto with hybrid.
(* apply c_wk_aeq2atp_tp; auto.
   apply atp_tp1 with T'; auto.
   apply aeqG2atpG_strengthen; auto.
   apply c_str_aeq2atp_atp; auto.
   apply c_wk_aeq2atp_tp; auto.
   apply atp_tp2 with T; auto.
   apply aeqG2atpG_strengthen; auto.
   apply c_str_aeq2atp_atp; auto. *)
Qed.

End promote_atp_adeq.

(************************)
(* Inversion Properties *)
(************************)
(* Specialized inversion properties of prog (could be automated) *)

Section aeq_inv.

Lemma ae_l_inv :
forall (i:nat) (Phi:list atm) (T T':uexp->uexp),
(forall x : uexp,
       proper x ->
       seq_ i Phi (Imp (aeq x x) (atom_ (aeq (T x) (T' x))))) ->
exists j:nat, (i=j+1 /\ 
 forall x : uexp,
       proper x ->
       seq_ j (aeq x x::Phi) (atom_ (aeq (T x) (T' x)))).
Proof.
induction i; auto.
intros Phi T T' H.
generalize (H (Var 0) (proper_Var 0)); intro H1.
inversion H1; clear H1; subst.
replace (i+1) with (S i) in H0; try omega.
intros Phi T T' H.
exists i; split; try omega.
intros x H0.
generalize (H x H0); intro H1.
inversion H1; clear H1; subst.
assert (i0 = i); try omega.
subst; auto.
Qed.

Lemma ae_tl_inv :
forall (i:nat) (Phi:list atm) (M N:uexp->uexp),
(forall a : uexp,
       proper a ->
       seq_ i Phi (Imp (atp a a) (atom_ (aeq (M a) (N a))))) ->
exists j:nat, (i=j+1 /\ 
 forall a : uexp,
       proper a ->
       seq_ j (atp a a::Phi) (atom_ (aeq (M a) (N a)))).
Proof.
induction i; auto.
intros Phi M N H.
generalize (H (Var 0) (proper_Var 0)); intro H1.
inversion H1; clear H1; subst.
replace (i+1) with (S i) in H0; try omega.
intros Phi M N H.
exists i; split; try omega.
intros a H0.
generalize (H a H0); intro H1.
inversion H1; clear H1; subst.
assert (i0 = i); try omega.
subst; auto.
Qed.

End aeq_inv.

(************)
(* Contexts *)
(************)

Section ctx_aeq_adeq.

(* Membership lemmas used in adequacy of aeq *)
Lemma memb_aeq_adeq1 : forall (Gamma:list atm) (T T':uexp),
  aeqG Gamma -> In (aeq T T') Gamma -> In (is_tm T) Gamma.
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; tauto).
injection h; intros; subst; subst; simpl; auto.
Qed.

Lemma memb_aeq_adeq2 : forall (Gamma:list atm) (T T':uexp),
  aeqG Gamma -> In (aeq T T') Gamma -> In (is_tm T') Gamma.
Proof.
intros Gamma T; induction 1; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; tauto).
intro h; simpl in h; destruct h as [h | [h | h]];
 try discriminate; try (simpl; tauto).
injection h; intros; subst; subst; simpl; auto.
Qed.

Lemma d_str_termaeq2term_term :
  forall (i:nat) (T x:uexp) (Gamma:list atm),
  seq_ i (is_tm x::aeq x x::Gamma) (atom_ (is_tm T)) ->
  seq_ i (is_tm x::Gamma) (atom_ (is_tm T)).
Proof.
intros i T x Gamma h.
apply term_strengthen_weaken with (is_tm x::aeq x x::Gamma); auto.
clear h T i.
intro T; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
clear h T i.
intro T; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

Lemma d_str_alphatp2alph_term :
  forall (i:nat) (T x:uexp) (Gamma:list atm),
  seq_ i (is_tp x::atp x x::Gamma) (atom_ (is_tm T)) ->
  seq_ i (is_tp x::Gamma) (atom_ (is_tm T)).
Proof.
intros i T x Gamma h.
apply term_strengthen_weaken with (is_tp x::atp x x::Gamma); auto.
clear h T i.
intro T; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
clear h T i.
intro T; simpl; split.
intros [h1 | [h1 | h1]]; try discriminate h1; auto.
intros [h1 | h1]; auto.
Qed.

End ctx_aeq_adeq.

(****************)
(* aeq Adequacy *)
(****************)

Section aeq_adeq.

Hint Resolve nil_aeq tcons_aeq acons_aeq memb_aeq_adeq1 memb_aeq_adeq2 : hybrid.

Lemma aeq_term :
  forall (i:nat) (T T':uexp) (Gamma:list atm),
  aeqG Gamma ->
  seq_ i Gamma (atom_ (aeq T T')) ->
  seq_ i Gamma (atom_ (is_tm T)) /\ seq_ i Gamma (atom_ (is_tm T')).
Proof.
intro i.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (T T':uexp) (Gamma:list atm),
     aeqG Gamma ->
     seq_ i Gamma (atom_ (aeq T T')) ->
     seq_ i Gamma (atom_ (is_tm T)) /\ seq_ i Gamma (atom_ (is_tm T')))).
intro H'.
apply H'; clear H' i; auto.
intros i h T T' Gamma cInv h1.
inversion h1; subst; clear h1.
inversion H0; subst; clear H0.
(* app case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
generalize h; intro h'.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
specialize h' with (1:=hi) (2:=cInv) (3:=H5).
elim h; intros h2 h3; elim h'; intros h4 h5; clear h h'.
split.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm M1)) (atom_ (is_tm M2)));
  auto with hybrid.
apply s_and; auto.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm N1)) (atom_ (is_tm N2)));
  auto with hybrid.
apply s_and; auto.
(* lam case *)
inversion H3; subst; clear H3.
generalize (ae_l_inv i Gamma M N H4); clear H4; intros [j [h1 h2]];
 subst.
assert (h':forall x:uexp, proper x -> 
        (seq_ j (is_tm x::aeq x x::Gamma) (atom_ (is_tm (M x))) /\
         seq_ j (is_tm x::aeq x x::Gamma) (atom_ (is_tm (N x))))).
intros x h1.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (aeq x x::Gamma); simpl; auto.
apply h2; auto.
split.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (M x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
apply s_imp; auto.
apply d_str_termaeq2term_term; auto.
generalize (h' x h5); tauto.
unfold seq_,atom_; apply s_bc with
  (All (fun x:uexp => (Imp (is_tm x) (atom_ (is_tm (N x))))));
  auto with hybrid.
apply s_all; auto.
intros x h5.
apply s_imp; auto.
apply d_str_termaeq2term_term; auto.
generalize (h' x h5); tauto.
(* tapp case *)
inversion H3; subst; clear H3.
assert (hi:i<i+1+1); try omega.
specialize h with (1:=hi) (2:=cInv) (3:=H4).
elim h; intros h2 h3; clear h.
specialize atp_tp_promote with (1:=cInv) (2:= H5); intros [h4 h5].
split.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm M)) (atom_ (is_tp A)));
  auto with hybrid.
apply s_and; auto.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_tm N)) (atom_ (is_tp B)));
  auto with hybrid.
apply s_and; auto.
(* tlam case *)
inversion H3; subst; clear H3.
generalize (ae_tl_inv i Gamma M N H4); clear H4; intros [j [h1 h2]];
 subst.
assert (h':forall a:uexp, proper a -> 
        (seq_ j (is_tp a::atp a a::Gamma) (atom_ (is_tm (M a))) /\
         seq_ j (is_tp a::atp a a::Gamma) (atom_ (is_tm (N a))))).
intros a h1.
apply h; eauto with hybrid; try omega.
apply seq_thin_exch with (atp a a::Gamma); simpl; auto.
apply h2; auto.
split.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (is_tp a) (atom_ (is_tm (M a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
apply s_imp; auto.
apply d_str_alphatp2alph_term; auto.
generalize (h' a h5); tauto.
unfold seq_,atom_; apply s_bc with
  (All (fun a:uexp => (Imp (is_tp a) (atom_ (is_tm (N a))))));
  auto with hybrid.
apply s_all; auto.
intros a h5.
apply s_imp; auto.
apply d_str_alphatp2alph_term; auto.
generalize (h' a h5); tauto.
(* context case *)
inversion cInv; subst.
split; apply s_init; eauto with hybrid.
   (* applied memb_aeq_adeq1 and memb_aeq_adeq2 *)
split; apply s_init; eauto with hybrid.
   (* applied memb_aeq_adeq1 and memb_aeq_adeq2 *)
Qed.

Lemma aeq_term_cor : forall T T':uexp, seq0 (atom_ (aeq T T')) ->
  (seq0 (atom_ (is_tm T)) /\ seq0 (atom_ (is_tm T'))).
Proof.
intros T T' [n h].
generalize nil_aeq; intro h1.
specialize aeq_term with (1:=h1) (2:=h); intros [h2 h3].
split; exists n; auto.
Qed.

End aeq_adeq.
