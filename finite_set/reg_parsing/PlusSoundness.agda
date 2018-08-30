open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module PlusSoundness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl ; null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool
open import Algebra.Logic
open import Data.Matrix
open import Data.Matrix.RingProperties
open import Data.Matrix.HelperTheorems
import NFA
open module nfalib = NFA ⅀ _≟_

helper6 : {k : ℕ}(m1 : 1 × k)(m2 : k × 1)(m3 : 1 × k)(m4 : k × k)
  → m1 ⋆ ((id ⊹ m2 ⋆ m3) ⋆ m4) ⋆ m2 ≡ [ [ true ] ]
  → m1 ⋆ m4 ⋆ m2 ≡ [ [ false ] ]
  → m3 ⋆ m4 ⋆ m2 ≡ [ [ true ] ]
helper6 m1 m2 m3 m4 p1 p2 with helper5 m1 m2 m3 m4 p1 p2
... | d 
  rewrite helper2 m1 m4 m2 m3 
  | mlaw1 (m1 ⋆ m4) (m1 ⋆ m2 ⋆ m3 ⋆ m4) m2
  | p2
  | mlaw6op (m1 ⋆ m2 ⋆ m3 ⋆ m4 ⋆ m2)
  | mlaw5  (m1 ⋆ m2) m3 m4
  | mlaw5  (m1 ⋆ m2) (m3 ⋆ m4) m2
  | d
  | idlaws (m3 ⋆ m4 ⋆ m2) = p1


plusmain4 : (nfa : NFA)(xs : List ⅀)(m1 m2 : 1 × (∇ nfa))
  → run (nfa +′) xs (m1 ⊹ m2) ⋆ (F nfa) ≡ 
    run (nfa +′) xs m1 ⋆ (F nfa) ⊹ run (nfa +′) xs m2 ⋆ (F nfa)
plusmain4 nfa [] m1 m2 rewrite mlaw1 m1 m2 (F nfa) = refl
plusmain4 nfa (x :: xs) m1 m2 
  rewrite mlaw1 m1 m2
    ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x)
  = plusmain4 nfa xs (m1 ⋆ ((id ⊹ F nfa ⋆ I nfa) ⋆
        δ nfa x)) (m2 ⋆ ((id ⊹ F nfa ⋆ I nfa) ⋆
        δ nfa x))


plusmain51  : (nfa : NFA)(xs : List ⅀)
  → run (nfa +′) xs (null {1} {_}) ≡ null {1} {_}
plusmain51 nfa [] = refl
plusmain51 nfa (x :: xs) 
  rewrite mlaw7op {_} {1} 
    ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x) 
  = plusmain51 nfa xs



plusmain5 : (nfa : NFA)(x x' x'' : ⅀)(xs : List ⅀)(m1 : 1 × 1)(m2 : 1 × (∇ nfa))
  → run (nfa +′) (x'' :: xs) (m1 ⋆ m2) ⋆ F nfa ≡ [ [ true  ] ]
  → m1 ≡ [ [ true ] ]
plusmain5 nfa x x' x'' xs m1 m2 p 
  with inspect' m1
... | it ((true ∷ []) ∷ []) prf1 rewrite prf1 = refl
... | it ((false ∷ []) ∷ []) prf1
  rewrite mlaw5 m1 m2 ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x'')
  | prf1
  | mlaw7op {1} {1} (m2 ⋆ ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x'')) 
  | plusmain51 nfa xs 
  | mlaw7op {_} {1} (F nfa) with p
... | () 



plusmain6 : (nfa : NFA)(x x' x'' : ⅀)(xs : List ⅀)(m1 : 1 × 1)(m2 : 1 × (∇ nfa))
  → run (nfa +′) (x'' :: xs) (m1 ⋆ m2) ⋆ F nfa ≡ [ [ true  ] ]
  → run (nfa +′) (x'' :: xs) (m1 ⋆ m2) ⋆ F nfa ≡ run (nfa +′) (x'' :: xs) m2 ⋆ F nfa
plusmain6 nfa x x' x'' xs m1 m2 p 
  with plusmain5 nfa x x' x'' xs m1 m2 p
... | d 
  rewrite mlaw5 m1 m2 ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x'')
  | d
  | idlaws (m2 ⋆ ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x'')) = refl


plusmain : (nfa : NFA)(x x' : ⅀)(xs : List ⅀)(sty : 1 × (∇ nfa))
  → run (nfa +′) (x' :: xs) (sty ⋆ δ nfa x) ⋆ F nfa ≡ [ [ true ] ]
  → run (nfa) (x :: x' :: xs) sty ⋆ F nfa ≡ [ [ false  ] ]
  → Σ[ s0 ∈ List ⅀ ] Σ[ s1 ∈ List ⅀ ] (x :: s0 +++  s1) ≡ (x :: x' :: xs)
       ⊗ run ( nfa) (x :: s0) sty ⋆ F nfa ≡ [ [ true ] ]
       ⊗ run (nfa +′) s1 (I nfa) ⋆ F nfa ≡ [ [ true ] ]

plusmain nfa x x' [] sty  p1 p2 = [] , x' :: [] , refl , 
  helper5 (sty ⋆ δ nfa x) (F nfa) (I nfa) (δ nfa x') p1 p2  , 
  trans (cong (λ q → q ⋆ F nfa) (helper1 (I nfa) (F nfa) (δ nfa x'))) (helper6 (sty ⋆ δ nfa x) (F nfa) (I nfa) (δ nfa x') p1 p2)


plusmain nfa x x' (x'' :: xs) sty  p1 p2 
  rewrite helper2 (sty ⋆ δ nfa x) (δ nfa x') (F nfa) (I nfa)
  | plusmain4 nfa (x'' :: xs) (sty ⋆ δ nfa x ⋆ δ nfa x') (sty ⋆ δ nfa x ⋆ F nfa ⋆ I nfa ⋆ δ nfa x')
  with inspect' 
   (run (nfa +′) (x'' :: xs) (sty ⋆ δ nfa x ⋆ F nfa ⋆ I nfa ⋆ δ nfa x') ⋆ F nfa)


plusmain nfa x x' (x'' :: xs) sty  p1 p2 | it ((true ∷ []) ∷ []) prf1
  rewrite mlaw5  (sty ⋆ δ nfa x ⋆ F nfa) (I nfa) (δ nfa x')
  = [] , x' :: x'' :: xs , refl , plusmain5 nfa x x' x'' xs (sty ⋆ δ nfa x ⋆ F nfa) (I nfa ⋆ δ nfa x') prf1 , 
   trans (trans ((cong (λ q → run (nfa +′) (x'' :: xs) q ⋆ F nfa) (helper1 (I nfa) (F nfa) (δ nfa x')))) (sym (plusmain6 nfa x x' x'' xs (sty ⋆ δ nfa x ⋆ F nfa) (I nfa ⋆ δ nfa x') prf1))) prf1





plusmain nfa x x' (x'' :: xs) sty  p1 p2 | it ((false ∷ []) ∷ []) prf1 rewrite prf1
  |  mlaw6 (run (nfa +′) (x'' :: xs) (sty ⋆ δ nfa x ⋆ δ nfa x') ⋆ F nfa)
    with plusmain nfa x' x'' xs (sty ⋆ δ nfa x) p1 p2
... | d1 , d2 , d3 , d4 , d5 = (x' :: d1) , d2 , trans (cong (_::_ x) d3) refl , d4 , d5


open <-on-length-Well-founded public

lemm3 : (xs ys : List ⅀)
  → length xs < (suc (length (xs +++ ys)))
lemm3 [] ys = lemm0
lemm3 (x :: xs) ys = lemm (lemm3 xs ys)

lenlem : (xs ys : List ⅀)
  → length (xs +++ ys) ≡ length xs ✚ length ys
lenlem [] ys = refl
lenlem (x :: xs) ys = cong (λ q → 1 ✚ q) (lenlem xs ys)

pluslenlem : (a b : ℕ) → a < ((suc b) ✚ a)
pluslenlem a nzero = <-base
pluslenlem a (suc n) = <-step (pluslenlem a n)

_≼_ : Rel' (List ⅀)
x ≼ y = length x < (length y)

plusmain-size : (nfa : NFA)(x : ⅀)(x' : ⅀)(xs : List ⅀)
 → (p1 : run (nfa +′) (x' :: xs) ((I nfa) ⋆ δ nfa x) ⋆ F nfa ≡ [ [ true ] ] )
 → (p2 : run (nfa) (x :: x' :: xs) (I nfa) ⋆ F nfa ≡ [ [ false ] ] )
 → (proj₁ (proj₂ (plusmain nfa x x' xs (I nfa) p1 p2)) ≼ (x :: x' :: xs))
plusmain-size nfa x x' xs p1 p2 with 
  plusmain nfa x x' xs (I nfa) p1 p2
... | d1 , [] , d3 , d4 , d5 = lemm0
plusmain-size nfa x .d2 .d2s p1 p2 | [] , (d2 :: d2s) , refl , d4 , d5 = <-base
plusmain-size nfa x .d1 .(d1s +++ d2s) p1 p2 | (d1 :: d1s) , d2s , refl , d4 , d5 
  rewrite lenlem (d1 :: d1s) d2s  = <-step (pluslenlem (foldrl (λ _ → suc) 0 d2s) (foldrl (λ _ → suc) 0 d1s) )

