
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

module EmptyCompleteness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix
open import Data.Matrix.RingProperties

import NFA
open module nfalib = NFA ⅀ _≟_


th : {m : ℕ}(s : List ⅀) → (e : RegExp) → s ◂ e → (runNFA (reg2nfa e) s) ≡ [ [ true ] ]
th .[] ε empt = refl
th _ _ _ = {!!}
