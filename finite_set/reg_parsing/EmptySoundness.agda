
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module EmptySoundness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec hiding (foldl) renaming (zipWith to devnull; map to devnull2)
open import Data.List renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix
open import Data.Matrix.RingProperties

import NFA
open module nfalib = NFA ⅀ _≟_



ε_sound_main : (xs : List ⅀)
  → foldl (λ v a → v ⋆ [ [ false ] ]) [ [ false ] ]
      xs ⋆ [ [ true ] ] ≡ [ [ false ] ]
ε_sound_main [] = refl
ε_sound_main (x :: xs) = ε_sound_main xs

{-
ε_sound : (s : List ⅀) → runNFA (reg2nfa ε) s ≡ [ [ true ] ] → s ◂ ε
ε_sound [] refl = empt
ε_sound (x :: xs) p rewrite (ε_sound_main xs) with p
... | ()
-}