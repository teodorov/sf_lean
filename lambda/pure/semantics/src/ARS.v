(** * Abstract Reduction Systems

    Useful lemmas when working with small-step reduction relations. *)
Require Import Setoid Equivalence Morphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope equiv_scope.

Delimit Scope prop_scope with PROP.
Open Scope prop_scope.

Notation "R <<= S" := (forall x y, R x y -> S x y)
  (at level 70, no associativity) : prop_scope.

Definition Pred X := X -> Prop.
Definition Rel  X := X -> Pred X.

(** **** Operators on relations *)
(**
We define the reflexive transitive closure (star)  and the equivalence closure (conv)
of a relation using inductive definitions. This differs from the presentation in the
lecture notes in two regards.

  - The definition of star is left recursive. This allows Coq to recognize that [x] is a
    parameter in [star R x y]. In particular, Coq generates the unary induction principle
    for this definition of star which simplifies the proofs in many places.
  - Having an inductive definition for the equivalence closure of a relation allows us to
    proof properties about it by induction on derivations. Compared to the definition of
    the equivalence closure as the reflexive transitive closure of the symmetric closure
    of a relation we avoid one level of indirection.
*)

Section Definitions.

Variables (X : Type) (R : Rel X).
Implicit Types (R S : Rel X) (x y z : X).

Inductive star x : Pred X :=
| starR : star x x
| starSR y z : star x y -> R y z -> star x z.

Inductive conv x : Pred X :=
| convR : conv x x
| convSR  y z : conv x y -> R y z -> conv x z
| convSRi y z : conv x y -> R z y -> conv x z.

Definition com R S := forall x y z, R x y -> S x z -> exists2 u, S y u & R z u.

Definition joinable R x y := exists2 z, R x z & R y z.
Definition diamond := forall x y z, R x y -> R x z -> exists2 u, R y u & R z u.
Definition confluent := forall x y z, star x y -> star x z -> joinable star y z.
Definition semi_confluent :=
  forall x y z, R x y -> star x z -> joinable star y z.
Definition CR := forall x y, conv x y -> joinable star x y.

Hint Resolve starR convR.

Lemma star1 x y : R x y -> star x y.
Proof. now apply starSR. Qed.

Lemma star_trans y x z : star x y -> star y z -> star x z.
Proof. induction 2; eauto using star. Qed.

Lemma starRS x y z : R x y -> star y z -> star x z.
Proof. intros rxy. apply star_trans. now apply star1. Qed.

Lemma star_conv x y : star x y -> conv x y.
Proof. induction 1; eauto using conv. Qed.

Lemma conv1 x y : R x y -> conv x y.
Proof. now apply convSR. Qed.

Lemma conv1i x y : R y x -> conv x y.
Proof. now apply convSRi. Qed.

Lemma conv_trans y x z : conv x y -> conv y z -> conv x z.
Proof. induction 2; eauto using conv. Qed.

Lemma convRS x y z : R x y -> conv y z -> conv x z.
Proof. intros rxy. apply conv_trans. now apply conv1. Qed.

Lemma convRSi x y z : R y x -> conv y z -> conv x z.
Proof. intros rxy. apply conv_trans. now apply conv1i. Qed.

Lemma conv_sym x y : conv x y -> conv y x.
Proof. induction 1; eauto using convRS, convRSi. Qed.

Lemma join_conv x y z : star x y -> star z y -> conv x z.
Proof.
  intros sxy szy. apply (@conv_trans y); [|apply conv_sym]; now apply star_conv.
Qed.

Lemma confluent_semi :
  confluent -> semi_confluent.
Proof.
  intros h x y z rxy sxz. apply (h x). now apply star1. assumption.
Qed.

Lemma semi_cr :
  semi_confluent -> CR.
Proof.
  intros semi x y. induction 1 as [|y z _ [u sxu syu] ryz|y z _ [u sxu syu]rzy].
  - now exists x.
  - destruct (semi y z u) as [v szv suv]; auto. exists v.
    + revert suv. now apply star_trans.
    + assumption.
  - exists u; eauto using starRS.
Qed.

Lemma cr_confluent :
  CR -> confluent.
Proof.
  intros cr x y z sxy sxz. apply cr. apply (@conv_trans x).
  - apply conv_sym. now apply star_conv.
  - now apply star_conv.
Qed.

End Definitions.

Hint Resolve starR convR.
Arguments star_trans {X R} y {x z} A B.
Arguments conv_trans {X R} y {x z} A B.

Lemma star_img X Y (f : X -> Y) (R : Rel X) S :
  (forall x y, R x y -> star S (f x) (f y)) ->
  (forall x y, star R x y -> star S (f x) (f y)).
Proof.
  intros A. induction 1; eauto using star_trans.
Qed.

Lemma star_hom X Y (f : X -> Y) (R : Rel X) (S : Rel Y) :
  (forall x y, R x y -> S (f x) (f y)) ->
  (forall x y, star R x y -> star S (f x) (f y)).
Proof.
  intros A. apply star_img. intros x y rxy. apply star1. now apply A.
Qed.

Lemma star_proper X (f : X -> X) (R : Rel X) :
  (forall x y, R x y -> R (f x) (f y)) ->
  forall x y, star R x y -> star R (f x) (f y).
Proof. apply star_hom. Qed.

Lemma star_proper2 X (f : X -> X -> X) (R : Rel X) :
  (forall x y z, R x y -> R (f x z) (f y z)) ->
  (forall x y z, R y z -> R (f x y) (f x z)) ->
  forall x x' y y', star R x x' -> star R y y' -> star R (f x y) (f x' y').
Proof.
  intros A B x x' y y' sxx' syy'. apply (@star_trans _ _ (f x y')).
  auto using star_proper. revert x x' sxx'. apply star_proper. auto.
Qed.

Lemma conv_img X Y (f : X -> Y) (R : Rel X) S :
  (forall x y, R x y -> conv S (f x) (f y)) ->
  (forall x y, conv R x y -> conv S (f x) (f y)).
Proof.
  intros A x y. induction 1; eauto using conv_trans, conv_sym.
Qed.

Lemma conv_hom X Y (f : X -> Y) (R : Rel X) (S : Rel Y) :
  (forall x y, R x y -> S (f x) (f y)) ->
  (forall x y, conv R x y -> conv S (f x) (f y)).
Proof.
  intros A. apply conv_img. intros x y rxy. apply conv1. now apply A.
Qed.

Arguments star_img {X Y} f R {S} A x y B.
Arguments star_hom {X Y} f R {S} A x y B.
Arguments conv_img {X Y} f R {S} A x y B.
Arguments conv_hom {X Y} f R {S} A x y B.

Lemma star_closure X (R S : Rel X) : R <<= star S -> star R <<= star S.
Proof. apply star_img. Qed.

Lemma star_monotone X (R S : Rel X) : R <<= S -> star R <<= star S.
Proof.
  intros A. apply star_closure. intros x y rxy. apply star1. now apply A.
Qed.

Lemma eq_star X (R S : Rel X) :
  R <<= star S -> S <<= star R -> star R === star S.
Proof. intros A B x y. split; now apply star_closure. Qed.

Lemma star_interpolation X (R S : Rel X) :
  R <<= S -> S <<= star R -> star R === star S.
Proof.
  intros A. apply eq_star. intros x y rxy. apply star1. now apply A.
Qed.

Lemma confluent_stable X (R S : Rel X) :
  star R === star S -> confluent R -> confluent S.
Proof.
  intros E conf x y z sxy sxz. apply E in sxy. apply E in sxz.
  destruct (conf x y z sxy sxz) as [u h1 h2]. exists u; now apply E.
Qed.

Lemma conv_closure X (R S : Rel X) : R <<= conv S -> conv R <<= conv S.
Proof. apply conv_img. Qed.

(** **** Commutation Properties *)
(** We show that confluence preserves diamond using commutation. *)

Section Commutation.
Variable X : Type.

Lemma com_strip (R S : Rel X) : com R S -> com (star S) R.
Proof.
  intros A x y z B rxy. induction B. now exists z.
  destruct IHB as [u ryu szu]. destruct (A _ _ _ ryu H) as [v h1 h2].
  exists v. assumption. eapply starSR. eassumption. assumption.
Qed.

Lemma com_lift (R S : Rel X) : com R S -> com (star R) (star S).
Proof. intros crs. apply com_strip. now apply com_strip. Qed.

Corollary diamond_confluent (R : Rel X) : diamond R -> confluent R.
Proof. apply com_lift. Qed.

End Commutation.

(** **** Weak and Strong Normalization *)

Section Termination.
Variables (X : Type) (R : Rel X).

Definition reducible x := exists y, R x y.
Definition normal x := ~ reducible x.

Definition nf x y := star R x y /\ normal y.
Definition wn x := exists y, nf x y.

Inductive sn x : Prop :=
| SNI : (forall y, R x y -> sn y) -> sn x.

Lemma sn_preimage (h : X -> X) x :
  (forall x y, R x y -> R (h x) (h y)) -> sn (h x) -> sn x.
Proof.
  intros H. remember (h x) as v. intros snv. revert x Heqv. induction snv.
  intros y eqn. subst. eauto using sn.
Qed.

Lemma normal_star x y : star R x y -> normal x -> x = y.
Proof.
  intros A B. induction A. reflexivity. subst. exfalso. apply B.
  now exists z.
Qed.

Hypothesis cr : CR R.

Lemma cr_star_normal x y : conv R x y -> normal y -> star R x y.
Proof.
  intros A. apply cr in A. destruct A as [z A B]. intros C.
  now rewrite (normal_star B C).
Qed.

Lemma cr_conv_normal x y : conv R x y -> normal x -> normal y -> x = y.
Proof.
  intros A. apply cr in A. destruct A as [z A B]. intros h1 h2.
  now rewrite (normal_star A h1), (normal_star B h2).
Qed.

End Termination.

(** **** Normalizing and CoFinal Strategies *)

Fixpoint iter {X} n (f : X -> X) (x : X) :=
  match n with
  | 0 => x
  | S m => f (iter m f x)
  end.

Section CoFinal.
Variables (X : Type) (R : Rel X) (rho : X -> X).

Definition normalizing :=
  forall x y, nf R x y -> exists n, y = iter n rho x.

Definition cofinal :=
  forall x y, star R x y -> exists n, star R y (iter n rho x).

Lemma cofinal_normalizing : cofinal -> normalizing.
Proof.
  intros A x y [h1 h2]. apply A in h1. destruct h1 as [n B].
  exists n. eapply normal_star; eauto.
Qed.

Definition triangle := forall x y, R x y -> R y (rho x).

Lemma triangle_diamond : triangle -> diamond R.
Proof.
  intros A x y z exy exz. exists (rho x); now apply A.
Qed.

Hypothesis tri : triangle.

Lemma triangle_monotone x y : R x y -> R (rho x) (rho y).
Proof. intros rxy. apply tri. now apply tri. Qed.

Lemma triangle_cofinal : cofinal.
Proof.
  intros x y. induction 1. now exists 0.
  destruct IHstar as [n ih]. exists (S n). simpl. apply (starRS (tri H0)).
  revert ih. apply star_img. intros a b rab. apply star1.
  now apply triangle_monotone.
Qed.

End CoFinal.

(** **** The Tait, Martin-Loef, Takahashi confluence proof method. *)

Lemma cr_method X (R S : Rel X) (rho : X -> X) :
  R <<= S -> S <<= star R -> triangle S rho -> CR R.
Proof.
  intros A B C. apply semi_cr. apply confluent_semi.
  assert (eqs : star R === star S). now apply star_interpolation.
  eapply confluent_stable. symmetry. eassumption.
  apply diamond_confluent. eapply triangle_diamond. eassumption.
Qed.

(** Setoid Instances *)

Instance subrel_star X (R : Rel X) : subrelation R (star R).
Proof. intros x y rxy. now apply star1. Qed.

Instance subrel_conv X (R : Rel X) : subrelation R (conv R).
Proof. intros x y rxy. now apply conv1. Qed.

Instance subrel_star_conv X (R : Rel X) : subrelation (star R) (conv R).
Proof. intros x y sxy. now apply star_conv. Qed.

(* Declaring these instances breaks setoid. *)
Lemma preorder_star X (R : Rel X) : PreOrder (star R).
Proof.
  constructor.
  - intros x. apply starR.
  - intros x y z. apply star_trans.
Qed.

Lemma equivalence_conv X (R : Rel X) : Equivalence (conv R).
Proof.
  constructor.
  - intros x. apply convR.
  - intros x y. apply conv_sym.
  - intros x y z. apply conv_trans.
Qed.

(** Uniform Confluence *)
(**
  In the lecture notes proofs about uniform confluence use plenty of arithmetic,
  which is a nightmare to formalize. Here we replace the arithmetic conditions on
  uniform confluence by an inductive definition of "uniform joinability" [uj].
*)

Definition uniform_confluent {X} (R : Rel X) :=
  forall x y z, R x y -> R x z -> y = z \/ joinable R y z.

Inductive starn X (R : Rel X) : nat -> Rel X :=
| starnxx x : starn R 0 x x
| starnRS n x y z : R x y -> starn R n y z -> starn R (S n) x z.

Inductive uj {X} (R : Rel X) : nat -> nat -> Rel X :=
| uj_refl x : uj R 0 0 x x
| uj_stepl x y z m n :
    R x y -> uj R m n y z -> uj R m (S n) x z
| uj_stepr x y z m n :
    uj R m n x y -> R z y -> uj R (S m) n x z
| uj_weaken x y m n :
    uj R m n x y -> uj R (S m) (S n) x y.
Hint Constructors uj.

Lemma starn_uj {X} (R : Rel X) n x y :
  starn R n y x -> uj R n 0 x y.
Proof. induction 1; eauto. Qed.

Lemma uj_extend {X} (R : Rel X) x y z m n :
  uniform_confluent R -> uj R m n x y -> R y z ->
  uj R m (S n) x z.
Proof.
  intros H uxy. revert z. induction uxy; eauto.
  intros u rzu. destruct (H _ _ _ H0 rzu).
  - subst. now apply uj_weaken.
  - destruct H1. eapply uj_stepr; eauto.
Qed.

Lemma uj_extendn {X} (R : Rel X) x y z m n k :
  uniform_confluent R -> uj R m n x y -> starn R k y z ->
  uj R m (k + n) x z.
Proof.
  intros h1 h2 h3. revert m n x h2. induction h3; eauto; intros; simpl.
  rewrite plus_n_Sm. apply IHh3. eauto using uj_extend.
Qed.

Lemma uf_uj {X} (R : Rel X) x y z m n :
  uniform_confluent R -> starn R m x y -> starn R n x z ->
  uj R m n y z.
Proof.
  intros h1 h2 h3. rewrite (plus_n_O n). eapply uj_extendn; eauto.
  now apply starn_uj.
Qed.

(* Uniform Church-Rosser *)

Inductive convmn {X} (R : Rel X) : nat -> nat -> Rel X :=
| convmnR   : forall x, convmn R 0 0 x x
| convmnSR  : forall m n x y z, convmn R m n x y -> R y z -> convmn R m (S n) x z
| convmnSRi : forall m n x y z, convmn R m n x y -> R z y -> convmn R (S m) n x z.

Lemma uf_ucr {X} (R : Rel X) x y m n :
  uniform_confluent R -> convmn R m n x y -> uj R m n x y.
Proof.
  intros H cxy. induction cxy; eauto using uj_extend.
Qed.

(* Uniform Normalization *)

Require Import Arith.Le Arith.Minus.

Lemma uj_normal_le X (R : Rel X) (x y : X) (m n : nat) :
  normal R y -> uj R m n x y -> m <= n.
Proof.
  intros H uxy. induction uxy; eauto.
  - exfalso. apply H. now exists y.
  - apply le_n_S. now apply IHuxy.
Qed.

Lemma uj_normal X (R : Rel X) (x y : X) (m n : nat) :
  normal R y -> uj R m n x y -> starn R (n-m) x y.
Proof with eauto using starn.
  intros H uxy. induction uxy...
  - rewrite <- minus_Sn_m... eauto using uj_normal_le.
  - exfalso. apply H. now exists y.
Qed.

Theorem uniform_normalization {X} (R : Rel X) (x y z : X) (m n : nat) :
  uniform_confluent R ->
  starn R m x y -> starn R n x z -> normal R z ->
  m <= n /\ starn R (n - m) y z.
Proof.
  intros h1 h2 h3 h4. generalize (uf_uj h1 h2 h3). intuition.
  - eauto using uj_normal_le.
  - eauto using uj_normal.
Qed.

(* Lecture notes definition of uniform joinability *)

Require Import Omega.

Inductive UniformConfluenceP {X} (R : Rel X) (y z : X) (m n : nat) : Prop :=
| UniformConfluenceI (u : X) (k l : nat) :
    starn R k y u -> starn R l z u ->
    m + k = n + l ->
    k <= n ->
    l <= m ->
    UniformConfluenceP R y z m n.

Lemma uj_UCP {X} (R : Rel X) (x y : X) (m n : nat) :
  uj R m n x y -> UniformConfluenceP R x y m n.
Proof with eauto using starn.
  induction 1...
  - exists x 0 0...
  - destruct IHuj. exists u (S k) l... omega. omega.
  - destruct IHuj. exists u k (S l)... omega. omega.
  - destruct IHuj. exists u k l... omega.
Qed.

Theorem italian_uniform_confluence {X} (R : Rel X) (x y z : X) (m n : nat) :
  uniform_confluent R ->
  starn R m x y -> starn R n x z -> exists u k l,
      starn R k y u /\ starn R l z u /\
      m + k = n + l /\ k <= n /\ l <= m.
Proof.
  intros h1 h2 h3. generalize (uf_uj h1 h2 h3). intros h4.
  apply uj_UCP in h4. destruct h4. exists u, k, l. intuition.
Qed.

(* Connecting uniform confluence to confluence *)

Lemma starn_trans X (R : Rel X) x y z m n :
  starn R m x y -> starn R n y z -> starn R (m + n) x z.
Proof. induction 1; simpl; eauto using starn. Qed.

Lemma starn_star X (R : Rel X) x y :
  star R x y <-> exists n, starn R n x y.
Proof.
  split.
  - induction 1; eauto using starn. destruct IHstar as [n ih].
    exists (S n). replace (S n) with (n + 1) by omega.
    eauto using starn, starn_trans.
  - intros [n sxy]. induction sxy; eauto using starRS.
Qed.

Lemma uj_joinable X (R : Rel X) m n x y :
  uj R m n x y -> joinable (star R) x y.
Proof with eauto using starRS.
  induction 1 as [x|x y z m n rxy _ [u ih1 ih2]|
                  x y z m n _ [u ih1 ih2] rzr|x y m n _ [u ih1 ih2]].
  exists x... exists u... exists u... exists u...
Qed.

Lemma uc_confluent X (R : Rel X) :
  uniform_confluent R -> confluent R.
Proof.
  intros H x y z sxy sxz. apply starn_star in sxy. destruct sxy as [m sxy].
  apply starn_star in sxz. destruct sxz as [n sxz]. eapply uj_joinable.
  eapply uf_uj; eassumption.
Qed.
