Require Import Basics UntypedLambda ARS Reduction.
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s t : term) (sigma tau : nat -> term) (xi : nat -> nat).

Inductive pstep : Rel term :=
| pstep_beta s s' t t' :
    pstep s s' -> pstep t t' ->
    pstep ((Lam s) t) s'.[t'/]
| pstep_app s s' t t' :
    pstep s s' -> pstep t t' ->
    pstep (s t) (s' t')
| pstep_lam s s' :
    pstep s s' ->
    pstep (Lam s) (Lam s')
| pstep_var x :
    pstep (Var x) (Var x).
Definition psteps sigma tau := forall x, pstep (sigma x) (tau x).

Fixpoint rho s :=
  match s with
  | App (Lam s) t => (rho s).[rho t/]
  | App s t => App (rho s) (rho t)
  | Lam s => Lam (rho s)
  | Var x => Var x
  end.

Lemma pstep_refl s : pstep s s.
Proof. induction s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. induction 1; eauto using pstep. Qed.

Lemma pstep_red s t : pstep s t -> red s t.
Proof with eauto using star1, step.
  intros st. induction st...
  - rewrite IHst1, IHst2...
  - rewrite IHst1, IHst2...
  - rewrite IHst...
Qed.

Lemma pstep_ren s t xi :
  pstep s t -> pstep s.[xi] t.[xi].
Proof with eauto using pstep.
  intros st. revert xi. induction st; simpl; intros...
  - rewrite <- subst_beta. apply pstep_beta...
    rewrite upr_up. apply IHst1.
  - rewrite upr_up...
Qed.

Lemma psteps_up sigma tau :
  psteps sigma tau -> psteps (up sigma) (up tau).
Proof.
  intros pst x. rewrite !upE; destruct x; simpl; eauto.
  now apply pstep_ren.
Qed.

Lemma pstep_subst s t sigma tau :
  pstep s t -> psteps sigma tau -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psteps_up.
  intros st. revert sigma tau. induction st; intros; simpl...
  rewrite <- subst_beta. apply pstep_beta...
Qed.

Lemma pstep_subst1 s s' t t' :
  pstep s s' -> pstep t t' -> pstep s.[t/] s'.[t'/].
Proof with eauto using pstep.
  intros p1 p2. apply pstep_subst... intros [|x]...
Qed.

Ltac inv H := inversion H; clear H; subst.

Ltac pstep_inv :=
  repeat match goal with
  | H : pstep (Lam _) _ |- _ => inv H
  | H : pstep (App _ _) _ |- _ => inv H
  | H : pstep (Var _) _ |- _ => inv H
  end.

Lemma rho_triangle :
  triangle pstep rho.
Proof with simpl; eauto using pstep, pstep_subst1.
  intros s t st. induction st... destruct s... pstep_inv...
Qed.

Theorem church_rosser :
  CR step.
Proof.
  apply (cr_method (S := pstep) (rho := rho)).
  - apply step_pstep.
  - apply pstep_red.
  - apply rho_triangle.
Qed.
