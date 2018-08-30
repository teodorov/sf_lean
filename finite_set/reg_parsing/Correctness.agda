
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module Correctness (⅀ : Set) (_≟_ : Decidable (_≡_ {A = ⅀}))  where
open import Data.Vec
open import Data.List hiding (null)
open import Data.Bool
open import Algebra.Logic
open import Data.Matrix
open import Data.Matrix.RingProperties
open import Data.Sum
open import Data.Empty

import NFA
open module nfalib = NFA ⅀ _≟_

import RegExp
open module regexp = RegExp ⅀ _≟_

import Completeness
open module complete = Completeness ⅀ _≟_

import Soundness
open module sound = Soundness ⅀ _≟_


parse : (u : String) → (e : RegExp) → u ◂ e ⊎ (u ◂ e → ⊥)
parse u e with inspect' (runNFA (reg2nfa e) u) 
parse u e | it ((true  ∷ []) ∷ []) run = inj₁ (sound u e run)
parse u e | it ((false ∷ []) ∷ []) run = inj₂ (λ tree → false≠true (trans (sym run) (complete  u e tree)) )
  where
    false≠true : null {1} {1} ≡ id {1} → ⊥
    false≠true ()

