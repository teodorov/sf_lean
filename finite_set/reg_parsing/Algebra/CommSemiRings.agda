
module Algebra.CommSemiRings where

open import Relation.Binary.PropositionalEquality


record CommSemiRing : Set₁ where
  field R      : Set
        _+_    : R → R → R
        _*_    : R → R → R
        one    : R
        zero   : R
        law1   : ∀{a b c} → (a + b) + c ≡ a + (b + c)
        law2   : ∀{a} → zero + a ≡ a
        law3   : ∀{a} → a + zero ≡ a
        law4   : ∀{a b} → a + b ≡ b + a
        law5   : ∀{a b c} → (a * b) * c ≡ a * (b * c)
        law6   : ∀{a} → one * a ≡ a
        law7   : ∀{a} → a * one ≡ a
        law8   : ∀{a b c} → a * (b + c) ≡ (a * b) + (a * c)
        law9   : ∀{a b c} → (a + b) * c ≡ (a * c) + (b * c)
        law10  : ∀{a} → zero * a ≡ zero
        law11  : ∀{a} → a * zero ≡ zero
        law12  : ∀{a}{b} → a * b ≡ b * a
--open CommSemiRing public

