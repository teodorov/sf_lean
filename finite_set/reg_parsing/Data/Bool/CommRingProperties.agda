
module Data.Bool.CommRingProperties where

open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Algebra.CommSemiRings

bsr_law1 : {a b c : Bool} → (a ∨ b) ∨ c ≡  a ∨ (b ∨ c)
bsr_law1 {true} = refl
bsr_law1 {false} = refl

bsr_law2 :  ∀{a} → false ∨ a ≡ a
bsr_law2 {true} = refl
bsr_law2 {false} = refl

bsr_law3 : ∀{a} → a ∨ false ≡ a
bsr_law3 {true} = refl
bsr_law3 {false} = refl

bsr_law4 : ∀{a b} → a ∨ b ≡ b ∨ a
bsr_law4 {true} {true} = refl
bsr_law4 {true} {false} = refl
bsr_law4 {false} {true} = refl
bsr_law4 {false} {false} = refl

bsr_law5 : ∀{a b c} → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
bsr_law5 {true} {true} {true} = refl
bsr_law5 {false} {true} {true} = refl
bsr_law5 {true} {false} {true} = refl
bsr_law5 {false} {false} {true} = refl
bsr_law5 {true} {b} {false} = refl
bsr_law5 {false} {b} {false} = refl

bsr_law6 : ∀{a} → true ∧ a ≡ a
bsr_law6 {a} = refl

bsr_law7 : ∀{a} → a ∧ true ≡ a
bsr_law7 {true} = refl
bsr_law7 {false} = refl

bsr_law8 : ∀{a b c} → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
bsr_law8 {true} {true} {true} = refl
bsr_law8 {false} {true} {true} = refl
bsr_law8 {true} {false} {true} = refl
bsr_law8 {false} {false} {true} = refl
bsr_law8 {true} {b} {false} = refl
bsr_law8 {false} {b} {false} = refl


bsr_law9 : ∀{a b c} → (a ∨ b) ∧ c ≡ (a ∧ c) ∨ (b ∧ c)
bsr_law9 {true} {true} {true} = refl
bsr_law9 {false} {true} {true} = refl
bsr_law9 {true} {false} {true} = refl
bsr_law9 {false} {false} {true} = refl
bsr_law9 {true} {true} {false} = refl
bsr_law9 {true} {false} {false} = refl
bsr_law9 {false} {b} {false} = refl

bsr_law10 : ∀{a} → false ∧ a ≡ false
bsr_law10 {a} = refl

bsr_law11 : ∀{a} → a ∧ false ≡ false 
bsr_law11 {true} = refl
bsr_law11 {false} = refl

bsr_law12 : ∀{a b} → a ∧ b ≡ b ∧ a 
bsr_law12 {true} {true} = refl
bsr_law12 {true} {false} = refl
bsr_law12 {false} {true} = refl
bsr_law12 {false} {false} = refl


bsr : CommSemiRing
bsr = record{
              _+_ = _∨_ ;
              _*_ = _∧_ ;
              one = true ;
              zero = false ;
              law1 = λ {a} {b} {c} → bsr_law1 {a} {b} {c} ;
              law2 =  bsr_law2 ;
              law3 =  bsr_law3 ;
              law4 = λ {a} {b} → bsr_law4 {a} {b} ;
              law5 = λ {a} {b} {c} → bsr_law5 {a} {b} {c} ;
              law6 = λ {a} → bsr_law6 {a} ; 
              law7 = λ {a} → bsr_law7 {a} ; 
              law8 = λ {a} {b} {c} → bsr_law8 {a} {b} {c} ;
              law9 = λ {a} {b} {c} → bsr_law9 {a} {b} {c} ;
              law10 = λ {a} → bsr_law10 {a} ; 
              law11 = λ {a} → bsr_law11 {a}   ; 
              law12 = λ {a} {b} → bsr_law12 {a} {b}
      }

--open bsr public

