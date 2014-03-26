(****************************************************************
   File: TypingSimple.v
   Authors: Amy Felty
   Version: Coq V8.4pl2
   Date: January 2014

   1. Type unicity (the R and G approach coincide since there is only
      one context)
   2. Adequacy (using R approach)

  ***************************************************************)

Require Export sl.

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

Inductive Econ: Set := Cabs: tp -> Econ | Capp: Econ.
Definition uexp : Set := expr Econ.

Definition Var : var -> uexp := (VAR Econ).
Definition Bnd : bnd -> uexp := (VAR Econ).
Definition lam : tp -> (uexp -> uexp) -> uexp :=
  fun t:tp => fun f:uexp->uexp =>
  (APP (CON (Cabs t)) (lambda f)).
Definition app : uexp -> uexp -> uexp :=
  fun e1:uexp => fun e2:uexp => (APP (APP (CON Capp) e1) e2).

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

Lemma proper_lam: forall (t:tp) (E:uexp -> uexp),
  abstr E -> proper (lam t (fun x => E x)).
Proof.
unfold lam; auto with hybrid.
Qed.

Lemma proper_app: forall (E1 E2:uexp),
  proper E1 -> proper E2 -> proper (app E1 E2).
Proof.
unfold app; auto with hybrid.
Qed.

Hint Resolve proper_Var : hybrid.

(****************************************************************
   The atm type and instantiation of oo.
  ****************************************************************)
Inductive atm : Set :=
   oft : uexp -> tp -> atm
 | is_term : uexp -> atm.

Definition oo_ := oo atm Econ.
Definition atom_ : atm -> oo_ := atom Econ.
Definition T_ : oo_ := T atm Econ.

Hint Unfold oo_ atom_ T_: hybrid.

(****************************************************************
   Contexts with Unique Variables
  ****************************************************************)

Definition nvA (a:atm) : var
  := match a with
       oft e t => (newvar e)
     | is_term e => (newvar e)
     end.

Lemma nvA_oft : forall (e:uexp) (t:tp),
  nvA (oft e t) = (newvar e).
Proof.
simpl; auto.
Qed.

Lemma nvA_term : forall (e:uexp), nvA (is_term e) = (newvar e).
Proof.
simpl; auto.
Qed.

Fixpoint nvC (l:list atm) {struct l} : var
  := match l with
       nil => 0
     | (a::l') => max (nvA a) (nvC l')
     end.

Lemma nvC_cons: forall (a:atm) (l:list atm),
  nvC (a::l) = max (nvA a) (nvC l).
Proof.
simpl; auto.
Qed.

Lemma greater_head_nvC : forall (v:var) (t:tp) (l:list atm),
  (nvC (oft (Var v) t::l)) > v.
Proof.
intros v t l; simpl.
assert (h:(exists n:nat, (nvC l)=n)).
exists (nvC l); auto.
elim h; clear h; intros n h; rewrite h; clear h.
case n; simpl; auto.
intro n0; rewrite max_SS.
generalize (max_dec (S v) (S n0)); intros [h | h].
rewrite h; omega.
generalize (max_le_l (S v) (S n0)).
rewrite h; omega.
Qed.

Lemma greater_nvC: forall (v:var) (t:tp) (l:list atm),
  (In (oft (Var v) t) l) -> (nvC l > v).
Proof.
induction l; try contradiction; auto.
(* cons case *)
generalize a; clear a; induction a; try contradiction; auto.
generalize u; clear u; induction u.
(* CON case *)
intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
  try discriminate h.
simpl; apply IHl; auto.
(* VAR case *)
intro h; specialize in_inv with (1:=h); clear h; intros [h | h].
unfold Var; injection h; intros; subst; clear h.
apply greater_head_nvC; auto.
generalize (IHl h); clear IHl h; intro h.
rewrite -> nvC_cons.
rewrite -> nvA_oft.
unfold newvar.
generalize (max_dec (S v0) (nvC l)); intros [h1 | h1].
generalize (max_le_r (S v0) (nvC l)).
rewrite h1; omega.
rewrite h1; auto.
(* BND case *)
intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
  try discriminate h.
simpl; apply IHl; auto.
(* APP case *)
intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
  try discriminate h.
simpl.
generalize (IHl h); intro h1.
generalize (max_le_r (max (newvar u1) (newvar u2)) (nvC l));
  intro h2.
omega.
(* ABS case *)
intro h; specialize in_inv with (1:=h); clear h; intros [h | h];
  try discriminate h.
simpl.
generalize (IHl h); intro h1.
generalize (max_le_r (newvar u) (nvC l)); intro h2.
omega.
(* term case *)
simpl; intros [h | h]; try discriminate h.
generalize (IHl h); intro h1.
generalize (max_le_r (newvar u) (nvC l)); omega.
Qed.

Lemma fresh_nvC: forall (v:var) (t:tp) (l:list atm),
  (In (oft (Var v) t) l) -> (nvC l <> v).
Proof.
intros v t l h; generalize (greater_nvC v t l); intro h1.
generalize (h1 h); intro; omega.
Qed.

(****************************************************************
   Definition of prog
  ****************************************************************)

Inductive prog : atm -> oo_ -> Prop :=
  | of_l :
      forall (A B:tp) (M:uexp -> uexp),
      abstr M ->
      prog (oft (lam A (fun x => M x)) (arr A B))
        (All (fun x : uexp => Imp (oft x A) (atom_ (oft (M x) B))))
  | of_a :
      forall M N: uexp, forall A B:tp,
      prog (oft (app M N) A)
        (Conj (atom_ (oft M (arr B A))) (atom_ (oft N B)))
  | tm_l : forall (A:tp) (M:uexp -> uexp),
      abstr M ->
      prog (is_term (lam A (fun x => (M x))))
        (All (fun x:uexp => (Imp (is_term x) (atom_ (is_term (M x))))))
  | tm_a : forall M N:uexp,
      prog (is_term (app M N))
        (Conj (atom_ (is_term M)) (atom_ (is_term N))).

Hint Resolve of_l of_a tm_l tm_a : hybrid.

(****************************************************************
   Instantiation of seq
  ****************************************************************)

Definition seq_ : nat -> list atm -> oo_ -> Prop := seq prog.
Definition seq'_ := seq' prog.
Definition seq0 (B : oo_) : Prop := exists i : nat, seq_ i nil B.

Hint Unfold seq_ seq'_ seq0: hybrid.

End encoding.

Hint Resolve level_CON level_VAR level_BND level_APP level_ABS : hybrid.
Hint Resolve proper_APP abstr_proper : hybrid.
Hint Unfold proper: hybrid.
Hint Rewrite ext_eq_eta : hybrid.
Hint Resolve proper_Var : hybrid.
Hint Resolve of_l of_a tm_l tm_a : hybrid.
Hint Unfold oo_ atom_ T_: hybrid.
Hint Unfold seq_ seq'_ seq0: hybrid.

(****************************************************************
 1. Type Uniqueness
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_uniq.

Inductive xtG : list atm -> Prop :=
| nil_t : xtG nil
| cons_t : forall (Phi_t:list atm) (t:tp),
    xtG Phi_t -> xtG (oft (Var (nvC Phi_t)) t::Phi_t).

Lemma memb_xtG_NoLam : forall (Phi_t:list atm) (E:uexp->uexp) (T T':tp),
  xtG Phi_t -> ~(In (oft (lam T E) T') Phi_t).
Proof.
intros Phi_t E T T'; induction 1; simpl; try tauto.
intro h; elim IHxtG.
destruct h as [h2 | h2]; try discriminate h2; auto.
Qed.

Lemma memb_xtG_NoApp : forall (Phi_t:list atm) (M N:uexp) (T:tp),
  xtG Phi_t -> ~(In (oft (app M N) T) Phi_t).
Proof.
intros Phi_t M N T; induction 1; simpl; try tauto.
intro h; elim IHxtG.
destruct h as [h2 | h2]; try discriminate h2; auto.
Qed.

Lemma memb_uniq : forall (Phi_t:list atm) (e:uexp) (t t':tp),
  xtG Phi_t ->
  In (oft e t) Phi_t -> In (oft e t') Phi_t ->
   (exists v:var, e = Var v) /\ t = t'.
Proof.
intros Phi_t e t t'; induction 1; try (simpl; tauto).
simpl; intros h1 h2; destruct h1 as [h1 | h1]; destruct h2 as [h2 | h2].
injection h1; injection h2; intros; subst; subst; simpl; split; auto.
exists (nvC Phi_t); auto.
injection h1; intros; subst; subst.
specialize fresh_nvC with (1:=h2); tauto.
injection h2; intros; subst; subst.
specialize fresh_nvC with (1:=h1); tauto.
auto.
Qed.

End ctx_uniq.

(****************************)
(* Main Lemmas and Theorems *)
(****************************)

Section uniq.

Hint Resolve memb_xtG_NoLam memb_xtG_NoApp nil_t cons_t : hybrid.

Lemma uniq : forall (i:nat) (Phi_t:list atm) (M:uexp) (A:tp),
  xtG Phi_t ->
  seq_ i Phi_t (atom_ (oft M A)) ->
  forall (k:nat) (B:tp), seq_ k Phi_t (atom_ (oft M B)) -> A = B.
Proof.
intros i Phi_t M A h1 h2 k B h3.
generalize
 (lt_wf_ind i
    (fun i:nat =>
     forall (Phi_t:list atm) (M:uexp) (A:tp),
     xtG Phi_t ->
     seq_ i Phi_t (atom_ (oft M A)) ->
     forall (k:nat) (B:tp), seq_ k Phi_t (atom_ (oft M B)) -> A = B)).
intro H'.
apply H' with Phi_t M k; clear H'; auto.
clear h1 h2 h3 i Phi_t M A B k.
intros i hInd Phi_t M A hCInv h1 k B h2.
inversion h1; subst.
inversion H0; subst; clear H0.
(* lam case *)
inversion H3; subst; clear H3.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
assert (h: proper (Var (nvC Phi_t))); auto with hybrid.
generalize (H2 (Var (nvC Phi_t)) h); clear H2; intro H2.
generalize (H6 (Var (nvC Phi_t)) h); clear H6; intro H6.
clear h; assert (h:ext_eq M0 M).
apply abstr_lam_simp_eta; auto.
unfold ext_eq in h.
assert (hp:proper (Var (nvC Phi_t))); auto with hybrid.
specialize h with (1:=hp).
rewrite <- h in H6; clear h H3 H7 M.
inversion H2; subst; clear H2.
inversion H6; subst; clear H6.
assert (hCInv':xtG (oft (Var (nvC Phi_t)) A0::Phi_t)); eauto with hybrid.
assert (h6: i0 < i0+1+1+1); try omega.
generalize (hInd i0 h6 (oft (Var (nvC Phi_t)) A0::Phi_t)
                 (M0 (Var (nvC Phi_t))) B0 hCInv' H3 i B1 H2);
  intro h7; rewrite h7; auto.
absurd (In (oft (lam A0 (fun x:uexp => M0 x)) B) (A'::L)); eauto with hybrid.
(* app case *)
inversion H3; subst; clear H3.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
inversion H3; subst; clear H3.
assert (h2: i < i+1+1); try omega.
generalize (hInd i h2 Phi_t M0 (arr B0 A) hCInv H4 i1 (arr B1 B) H6);
  intro h4.
inversion h4; auto.
absurd (In (oft (app M0 N) B) (A'::L)); eauto with hybrid.
(* context case *)
generalize hCInv; intro h'.
inversion h'; subst.
specialize memb_uniq with (1:=hCInv) (2:=H2) (3:=H2);
 intros [[v h3] h4]; clear h4; subst.
inversion h2; subst; clear h2.
inversion H1.
specialize memb_uniq with (1:=hCInv) (2:=H2) (3:=H3);
 intros [h3 h4]; subst; auto.
Qed.

Lemma uniq_cor: forall (M:uexp) (A B:tp),
  seq0 (atom_ (oft M A)) -> seq0 (atom_ (oft M B)) -> (A=B).
Proof.
intros M A B h1 h2.
unfold seq0 in h1; elim h1; clear h1; intros i h1.
unfold seq0 in h2; elim h2; clear h2; intros k h2.
apply uniq with i (nil:list atm) M k; eauto with hybrid.
Qed.

End uniq.

(****************************************************************
 2. Adequacy
  ****************************************************************)

(************)
(* Contexts *)
(************)

Section ctx_adeq.

Inductive xtR : list atm -> list atm -> Prop :=
| nil_xt : xtR nil nil
| cons_xt : forall (Phi_x Phi_t:list atm) (x:uexp) (t:tp),
    xtR Phi_x Phi_t ->
    xtR (is_term x::Phi_x) (oft x t::Phi_t).

Lemma memb_adeq : forall (Phi_x Phi_t:list atm) (E:uexp) (T:tp),
  xtR Phi_x Phi_t -> In (oft E T) Phi_t -> In (is_term E) Phi_x.
Proof.
intros Phi_x Phi_t E B; induction 1; try (simpl; tauto).
intro h2; simpl in h2; destruct h2 as [h2 | h2].
injection h2; intros; subst; subst; simpl; auto.
simpl; right; auto with hybrid.
Qed.

End ctx_adeq.

(****************)
(* oft Adequacy *)
(****************)

Section of_adeq.

Hint Resolve memb_adeq nil_xt cons_xt : hybrid.

Lemma of_adeq :
  forall (i:nat) (M:uexp) (A:tp) (Phi_x Phi_t:list atm),
  xtR Phi_x Phi_t ->
  seq_ i Phi_t (atom_ (oft M A)) ->
  seq_ i Phi_x (atom_ (is_term M)).
Proof.
intro i.
generalize
 (lt_wf_ind i
   (fun i:nat =>
    forall (M : uexp) (A : tp) (Phi_x Phi_t : list atm),
    xtR Phi_x Phi_t ->
    seq_ i Phi_t (atom_ (oft M A)) -> seq_ i Phi_x (atom_ (is_term M)))).
intro H'.
apply H'; clear H' i; auto.
intros i h M A Phi_x Phi_t h1 h2.
inversion h2; subst; clear h2.
inversion H0; subst; clear H0.
(* lam case *)
inversion H3; subst; clear H3.
unfold seq_,atom_; apply s_bc with
 (All (fun x:uexp => (Imp (is_term x) (atom_ (is_term (M0 x))))));
 auto with hybrid.
apply s_all; auto.
intros x h2.
generalize (H2 x h2); clear H2; intro H2.
inversion H2; subst; clear H2.
apply s_imp; auto.
apply h with B (oft x A0::Phi_t); eauto with hybrid; try omega.
(* app case *)
inversion H3; subst; clear H3.
unfold seq_,atom_;
  apply s_bc with (Conj (atom_ (is_term M0)) (atom_ (is_term N)));
  auto with hybrid.
apply s_and; auto.
apply h with (arr B A) Phi_t; auto; try omega.
apply h with B Phi_t; auto; try omega.
(* context case *)
inversion h1; subst.
apply s_init; eauto with hybrid.
Qed.

Lemma of_adeq_cor : forall (M:uexp) (A:tp),
  seq0 (atom_ (oft M A)) ->
  seq0 (atom_ (is_term M)).
Proof.
intros M A [n h].
generalize nil_xt; intro h1.
specialize of_adeq with (1:=h1) (2:=h); intro h2.
exists n; auto.
Qed.

End of_adeq.
