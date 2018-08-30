
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Algebra.CommSemiRings

module NFA (⅀ : Set)
            (_≟_ : Decidable (_≡_ {A = ⅀})) where


open import Data.Vec  hiding (foldl ; zipWith ; map)
open import Data.List hiding (drop ; zipWith ; map ; replicate ; foldr 
                             ; take ; reverse ; splitAt ; [_] ; null) 
                      renaming ( _++_ to _+++_; _∷_ to _::_)
open import Data.Nat  renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Data.Matrix

-- synonym 
String : Set
String = List ⅀


{- NFA record type definition -}
record NFA : Set where
 field ∇ : ℕ 
       δ  : ⅀ → ∇ × ∇
       I  : 1 × ∇
       F  : ∇ × 1
open NFA public


-- running NFA with parametrized start states
run : (nfa : NFA) → String → 1 × (∇ nfa) → 1 × (∇ nfa)
run nfa u I = foldl (λ A x → A ⋆ (δ nfa x)) I u

-- running NFA from initial states
runNFA : NFA → String → 1 × 1
runNFA nfa u = (run nfa u (I nfa)) ⋆ F nfa


-- main regular transformation of automata 
-- (used also in conversion from regular expressions to NFA)
_∪′_ : NFA → NFA → NFA
_∪′_ nfa₁ nfa₂ = record {
          δ = λ x → ⟦ ⟦ (δ nfa₁ x)         ∣  null     ⟧  /
                       ⟦ null {_} {∇ nfa₁} ∣ (δ nfa₂ x) ⟧ ⟧ ;
          F = F nfa₁ ++ F nfa₂ ; 
          ∇ = ∇ nfa₁ ✚ ∇ nfa₂ ; 
          I = ⟦ I nfa₁ ∣  I nfa₂ ⟧
          }


_○′_ : NFA → NFA → NFA
_○′_ nfa₁ nfa₂ = record {
             ∇ = ∇ nfa₁ ✚ ∇ nfa₂ ;
             δ   = λ x →  
                     ⟦ ⟦ δ nfa₁ x / null ⟧ ∣ 
                       ⟦ (F nfa₁) ⋆ (I nfa₂) / id ⟧ ⋆ (δ nfa₂ x) ⟧ ;
             F   = ⟦ (F nfa₁)  ⋆ ((I nfa₂) ⋆ (F nfa₂)) /
                                 F nfa₂                ⟧ ;
             I   = ⟦ I nfa₁ ∣ null {_} {∇ nfa₂} ⟧ }

_+′ : NFA → NFA 
nfa +′ = record {
        ∇ = ∇ nfa ;
        δ = λ x → (id ⊹ ((F nfa) ⋆ (I nfa ))) ⋆ (δ nfa x) ;
        F = F nfa ;
        I = I nfa } 

