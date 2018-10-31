Require Import ARS.
Set Implicit Arguments.
Unset Strict Implicit.

Inductive term :=
| Var (n : nat)
| App (s t : term)
| Lam (s : term).

Definition eqn (m n : nat) : {n = m} + {n <> m}.
Proof. decide equality. Qed.

Fixpoint substk (k : nat) (t : term) (s : term) : term :=
  match s with
  | Var n => if eqn n k then t else Var n
  | App s1 s2 => App (substk k t s1) (substk k t s2)
  | Lam s => Lam (substk (S k) t s)
  end.

Inductive step : term -> term -> Prop :=
| step_beta s t :
    step (App (Lam s) (Lam t)) (substk 0 (Lam t) s)
| step_appl s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appr s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2).

Definition uc {X} (R : X -> X -> Prop) :=
  forall x y z, R x y -> R x z -> y = z \/ exists2 u, R y u & R z u.

Ltac inv H := inversion H; clear H; subst.

Ltac invstep :=
  repeat match goal with
  | H : step (Lam _) _ |- _ => inv H
  | H : step (App _ _) _ |- _ => inv H
  | H : step (Var _) _ |- _ => inv H
  end.

(* Manual proof *)
(*
Lemma L_uniform_confluent :
  uniform_confluent step.
Proof.
  intros x y z rxy. revert z. induction rxy; intros z sxz.
  - invstep. tauto.
  - invstep.
    + destruct (IHrxy _ H2). subst. tauto. right. destruct H as [u].
      exists (App u t); eauto using step.
    + right. exists (App s2 t2); eauto using step.
  - invstep.
    + right. exists (App s2 t2); eauto using step.
    + destruct (IHrxy _ H2). subst. tauto. right. destruct H as [u].
      exists (App s u); eauto using step.
Qed.
*)

(* Automated proof *)
Lemma L_uniform_confluent :
  uc step.
Proof with try subst; invstep; eauto using step.
  intros x y z sxy. revert z. induction sxy; intros z sxz...
  - destruct (IHsxy _ H2)... destruct H...
  - destruct (IHsxy _ H2)... destruct H...
Qed.

Lemma L_confluent :
  confluent step.
Proof.
  apply uc_confluent, L_uniform_confluent.
Qed.
