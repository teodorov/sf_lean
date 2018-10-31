Require Import Basics UntypedLambda ARS.
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s t : term) (sigma tau : nat -> term) (xi : nat -> nat).

Inductive step : Rel term :=
| step_beta s t :
    step ((Lam s) t) s.[t/]
| step_appl s s' t :
    step s s' -> step (s t) (s' t)
| step_appr s t t' :
    step t t' -> step (s t) (s t')
| step_lam s s' :
    step s s' -> step (Lam s) (Lam s').
Notation red  := (star step).
Notation conv := (conv step).

Instance preorder_red : PreOrder red. apply preorder_star. Qed.
Instance equiv_conv : Equivalence conv. apply equivalence_conv. Qed.

(** Substitutivity *)

Hint Constructors star ARS.conv step.

Lemma step_ebeta s t u : s.[t/] = u -> step ((Lam s) t) u.
Proof. intros. subst. apply step_beta. Qed.

Lemma substitutivity s t :
  step s t -> forall sigma, step s.[sigma] t.[sigma].
Proof.
  induction 1; simpl; intros; eauto. apply step_ebeta. apply subst_beta.
Qed.

Lemma red_substitutivity sigma s t :
  red s t -> red s.[sigma] t.[sigma].
Proof.
  induction 1; eauto using substitutivity.
Qed.

Lemma conv_substitutivity sigma s t :
  s === t -> s.[sigma] === t.[sigma].
Proof.
  induction 1; eauto using substitutivity.
Qed.

(** Compatibility lemmas *)

Instance red_app : Proper (red ++> red ++> red) App.
Proof with eauto.
  intros s s' rs t t' rt. transitivity (s' t).
  induction rs... induction rt...
Qed.

Instance red_lam : Proper (red ++> red) Lam.
Proof.
  intros s s' rs. induction rs; eauto.
Qed.

Instance conv_app : Proper (conv ==> conv ==> conv) App.
Proof with eauto.
  intros s s' es t t' et. transitivity (s' t).
  induction es... induction et...
Qed.

Instance conv_lam : Proper (conv ==> conv) Lam.
Proof.
  intros s s' es. induction es; eauto.
Qed.

Lemma red_compat sigma tau s :
  (forall n, red (sigma n) (tau n)) -> red s.[sigma] s.[tau].
Proof.
  revert sigma tau. induction s; simpl; intros; eauto.
  - now rewrite IHs1, IHs2.
  - rewrite IHs. reflexivity. intros [|n]; simpl; eauto.
    rewrite !rename_subst. now apply red_substitutivity.
Qed.

Lemma conv_compat sigma tau s :
  (forall n, sigma n === tau n) -> s.[sigma] === s.[tau].
Proof.
  revert sigma tau. induction s; simpl; intros; eauto.
  - now rewrite IHs1, IHs2.
  - rewrite IHs. reflexivity. intros [|n]; simpl; eauto.
    rewrite !rename_subst. now apply conv_substitutivity.
Qed.

Instance red_subst_proper : Proper (pointwise_relation nat red ++> red ++> red) subst.
Proof.
  intros sigma tau rsubst s s' rterm. transitivity s'.[sigma].
  - now apply red_substitutivity.
  - now apply red_compat.
Qed.

Instance conv_subst_proper : Proper (equiv ==> equiv ==> equiv) subst.
Proof.
  intros sigma tau esubst s s' eterm. transitivity s'.[sigma].
  - now apply conv_substitutivity.
  - now apply conv_compat.
Qed.
