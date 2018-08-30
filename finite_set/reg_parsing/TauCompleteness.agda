
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

module TauCompleteness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix

import NFA
open module nfalib = NFA ⅀ _≟_


taulem : (x : ⅀) → (p : x ≡ x)
  → x ≟ x ≡ yes p
taulem x p with x ≟ x
taulem x refl | yes refl = refl
taulem x p | no ¬p with ¬p p
... | ()
