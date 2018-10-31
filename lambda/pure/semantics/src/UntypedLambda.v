(** Untyped lambda terms in de Bruijn representation *)
Require Import Setoid Equivalence Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Open Scope equiv_scope.

Inductive term :=
| Var (x : nat)
| App (s t : term)
| Lam (s : term).
Coercion Var : nat >-> term.
Coercion App : term >-> Funclass.

Implicit Types (s t : term) (sigma tau : nat -> term) (xi : nat -> nat).

(** Function composition *)

Definition funcomp {A B C : Type} (f : A -> B) (g : B -> C) x := g(f(x)).
Arguments funcomp {A B C} f g x /.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.

Reserved Notation "sigma >> tau" (at level 56, left associativity).
Notation "f >>> g" := (funcomp f g)
  (at level 56, left associativity) : subst_scope.

(** Stream cons *)

Definition scons {X : Type} (s : X) (xs : nat -> X) (x : nat) : X :=
  match x with S y => xs y | _ => s end.
Notation "s .: xr" := (scons s xr)
  (at level 55, sigma at level 56, right associativity) : subst_scope.

Lemma scons_comp X Y (x : X) (f : nat -> X) (g : X -> Y) :
  (x .: f) >>> g === (g x) .: (f >>> g).
Proof. intros [|n]; reflexivity. Qed.

(** Instantiation *)

Definition upr xi := 0 .: (xi >>> S).

Fixpoint rename xi s : term :=
  match s with
  | Var n => xi n
  | App s t => App (rename xi s) (rename xi t)
  | Lam s => Lam (rename (upr xi) s)
  end.

Definition up sigma := Var 0 .: (sigma >>> rename S).
Arguments up sigma x /.

Fixpoint subst sigma s :=
  match s with
  | Var n => sigma n
  | App s t => App (subst sigma s) (subst sigma t)
  | Lam s => Lam (subst (up sigma) s)
  end.

Definition ren xi := xi >>> Var.

Definition scomp sigma tau := sigma >>> subst tau.
Arguments scomp sigma tau x /.
Notation "sigma >> tau" := (scomp sigma tau).

Notation "s .[ sigma ]" := (subst sigma s)
  (at level 2, sigma at level 200, left associativity,
   format "s .[ sigma ]" ) : subst_scope.
Notation "s .[ t /]" := (subst (t .: Var) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]") : subst_scope.

(** Extensionality properties *)

Instance subst_proper :
  Proper (pointwise_relation nat eq ==> eq ==> eq) subst.
Proof.
  intros sigma tau eq1 s t eq2. subst t. revert sigma tau eq1.
  induction s; simpl; intros.
  - apply eq1.
  - f_equal. now apply IHs1. now apply IHs2.
  - f_equal. apply IHs. intros [|n]; simpl. reflexivity.
    unfold up. simpl. now rewrite eq1.
Qed.

Instance scomp_proper :
  Proper (pointwise_relation nat eq ==> pointwise_relation nat eq ==> pointwise_relation nat eq) scomp.
Proof.
  intros sigma sigma' eq1 tau tau' eq2 n. unfold scomp. simpl.
  now rewrite eq1, eq2.
Qed.

Instance scons_proper X :
  Proper (eq ==> pointwise_relation nat eq ==> pointwise_relation nat eq) (@scons X).
Proof.
  intros x y eq1 xs ys eq2 [|n]; simpl. apply eq1. apply eq2.
Qed.

(** Renaming is a special case of substitution *)

Lemma upr_up xi : up xi === upr xi.
Proof. now intros []. Qed.

Lemma rename_subst xi :
  rename xi === subst xi.
Proof.
  intros s. revert xi. induction s; simpl; intros.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - now rewrite IHs, <- upr_up.
Qed.

Lemma upE sigma :
  up sigma === Var 0 .: (sigma >> S).
Proof.
  intros [|x]; simpl; auto. apply rename_subst.
Qed.

(** Var is the identity substitution *)

Lemma up_id : up Var === Var.
Proof. now intros []. Qed.
  
Lemma subst_id s : s.[Var] = s.
Proof.
  induction s; simpl; eauto. now rewrite IHs1, IHs2.
  now rewrite up_id, IHs.
Qed.

(** Instantiation/Composition of substitutions forms a monoid action *)

Lemma subst_ren sigma xi s :
  s.[xi].[sigma] = s.[xi >>> sigma].
Proof.
  revert sigma xi. induction s; simpl; intros.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - rewrite upr_up, IHs. unfold upr. now rewrite scons_comp.
Qed.

Lemma ren_subst xi sigma s :
  s.[sigma].[xi] = s.[sigma >> xi].
Proof.
  revert xi sigma. induction s; simpl; intros.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - rewrite upr_up, IHs. do 2 f_equiv; intros [|n]; simpl.
    reflexivity. now rewrite !rename_subst, !subst_ren.
Qed.

Lemma up_comp sigma tau :
  up sigma >> up tau === up (sigma >> tau).
Proof.
  intros [|n]; simpl. reflexivity. rewrite !rename_subst.
  rewrite subst_ren, ren_subst. f_equiv; intros m. simpl.
  apply rename_subst.
Qed.

Lemma subst_comp sigma tau s :
  s.[sigma].[tau] = s.[sigma >> tau].
Proof.
  revert sigma tau. induction s; simpl; intros.
  - reflexivity.
  - now rewrite IHs1, IHs2.
  - now rewrite IHs, up_comp.
Qed.

(** Derived substitution lemmas *)

Lemma scons_scomp s sigma tau :
  (s .: sigma) >> tau === s.[tau] .: (sigma >> tau).
Proof. now intros []. Qed.

Lemma subst_extend sigma s :
  up sigma >> (s .: Var) === s .: sigma.
Proof.
  rewrite upE, scons_scomp; intros [|n]; simpl.
  - reflexivity.
  - now rewrite subst_comp, subst_id.
Qed.

Lemma subst_beta s t sigma :
  s.[up sigma].[t.[sigma]/] = s.[t/].[sigma].
Proof.
  now rewrite !subst_comp, subst_extend, scons_scomp.
Qed.
