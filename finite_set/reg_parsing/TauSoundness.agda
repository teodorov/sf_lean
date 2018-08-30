
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

module TauSoundness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec hiding (foldl) renaming (zipWith to devnull; map to devnull2)
open import Data.List  renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix
open import Data.Matrix.RingProperties


import NFA
open module nfalib = NFA ⅀ _≟_ 

import RegExp
open module regexp = RegExp ⅀ _≟_


τ_sound_main : (a : ⅀)(xs : List ⅀)
  → foldl (λ v a' → v ⋆ δ (reg2nfa (′ a)) a')
     ((false ∷ false ∷ []) ∷ []) xs ≡ ((false ∷ false ∷ []) ∷ [])
τ a sound [] main = refl
τ a sound x :: xs main with a ≟ x
... | yes p = τ_sound_main a xs
... | no ¬p  = τ_sound_main a xs

