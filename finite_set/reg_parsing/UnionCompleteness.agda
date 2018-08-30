
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core

module UnionCompleteness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where
open import Data.Vec hiding (foldl) renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl ; null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; 
                                              replicate to replicatel; foldr to foldrl; take to takel; 
                                              reverse to reversel; splitAt to splitAtl; _++_ to _+++_; 
                                              _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool
open import Algebra.Logic
open import Algebra.CommSemiRings
open import Data.Matrix
open import Data.Matrix.RingProperties
import NFA
open module nfalib = NFA ⅀ _≟_



union-splitplus1 : {l n : ℕ}(x : Vec Bool l)(x0 : Vec Bool n)(x' : Vec Bool l)(x1 : Vec Bool n)
  → zipWith _∨_ (x ++ x0) (x' ++ x1) ≡ (zipWith _∨_ x x' ++ zipWith _∨_ x0 x1)
union-splitplus1 [] x0 [] x1 = refl
union-splitplus1 (x ∷ xs) x0 (x' ∷ xs') x1 = cong (_∷_ _) (union-splitplus1 xs x0 xs' x1)


union-splitplus : {k l n : ℕ} → (a c : k × l) → (b d : k × n)
  → a ++++ b ⊹ c ++++ d ≡ (a ⊹ c) ++++ (b ⊹ d)
union-splitplus [] [] [] [] = refl
union-splitplus (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (x1 ∷ xs1) 
 rewrite union-splitplus1 x x0 x' x1 = cong (_∷_ _) (union-splitplus xs xs' xs0 xs1)



union-split : (nfa₁ nfa₂ : NFA)(u : String)(I₁ : 1 × _)(I₂ : 1 × _)
  → run (nfa₁ ∪′ nfa₂) u ⟦ I₁ ∣ I₂ ⟧ ≡ 
       ⟦ run nfa₁ u I₁ ∣ run nfa₂ u I₂ ⟧
union-split nfa1 nfa2 [] s s' = refl
union-split nfa1 nfa2 (x :: xs) s s' 
  rewrite con-⊗-stack s s' (zipWith _++_ (δ nfa1 x) (replicate (replicate false))) (zipWith _++_ (null {_} {∇ nfa1} ) (δ nfa2 x))
  | concatsup11 s (δ nfa1 x) (null {_} {∇ nfa2})
  | concatsup11 s' (null {_} {∇ nfa1}) (δ nfa2 x)
  | mlaw7 {_} {_} {∇ nfa2} s
  | mlaw7 {_} {_} {∇ nfa1} s' 
  | union-splitplus (s ⋆ δ nfa1 x) null null (s' ⋆ δ nfa2 x)
  | mlaw6 (s ⋆ δ nfa1 x)
  | mlaw21 (s' ⋆ δ nfa2 x)
   = union-split nfa1 nfa2 xs (s ⋆ δ nfa1 x) (s' ⋆ δ nfa2 x)
