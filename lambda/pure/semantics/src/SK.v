Require Import ARS.
Set Implicit Arguments.
Unset Strict Implicit.

(* Proof first done by Fabian Kunze, 20 November 2015 *)

Inductive term : Type :=
| Var : nat -> term
| K   : term
| S   : term
| App : term -> term -> term.

Coercion App : term >-> Funclass.
Implicit Types s t u : term. 

Reserved Notation "s '>>' t" (at level 50).
Inductive pstep : term -> term -> Prop :=
| pstepR s :
    s >> s
| pstepK s s' t:
    s >> s' -> K s t >> s'
| pstepS s s' t t' u u' :
    s >> s' -> t >> t' -> u >> u' ->  S s t u >> s' u' (t' u')
| pstepA s s' t t' :
    s >> s' -> t >> t' -> s t >> s' t'
where "s '>>' t" := (pstep s t).

Fixpoint rho s :=
  match s with
  | App (App K s) t => rho s
  | App (App (App S s) t) u => (rho s) (rho u) ((rho t) (rho u))
  | App s t => (rho s) (rho t)
  | u => u
  end.

Functional Scheme rho_ind := Induction for rho Sort Prop.

Ltac inv H := inversion H; clear H; subst.

Ltac inv_pstep :=
  match goal with
    | H : pstep (Var _) _ |- _ => inv H
    | H : pstep (App _ _) _ |- _ => inv H
    | H : pstep  K _     |- _ => inv H
    | H : pstep  S _     |- _ => inv H
  end.

Lemma rho_triangle :
  triangle pstep rho.
Proof.
  intros s. apply rho_ind; intros; subst;
  do 4 (inv_pstep; auto using pstep).
Qed.

Inductive step : term -> term -> Prop :=
| stepK s t : K s t > s
| stepS s t u : S s t u > s u (t u)
| stepAL s s' t : s > s' -> s t > s' t
| stepAR s t t' : t > t' -> s t > s t'
where "s '>' t" := (step s t).

Notation "s '>*' t" := (star step s t) (at level 50).

Lemma step_pstep s t :
  s > t -> s >> t.
Proof.
  induction 1; auto using pstep.
Qed.

Lemma step_star_comp s s' t t' :
  s >* s' -> t >* t' -> s t >* s' t'.
Proof.
  apply star_proper2; now constructor.
Qed.

Lemma pstep_star_step s t :
  s >> t -> s >* t.
Proof.
  induction 1.
  - apply starR.
  - eapply starRS. econstructor. assumption.
  - eapply starRS. econstructor. auto using step_star_comp.
  - auto using step_star_comp.
Qed.

Theorem church_rosser :
  CR step.
Proof.
  apply (cr_method (S := pstep) (rho := rho)).
  - apply step_pstep.
  - apply pstep_star_step.
  - apply rho_triangle.
Qed.
