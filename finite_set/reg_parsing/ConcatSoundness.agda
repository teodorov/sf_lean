
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module ConcatSoundness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl ; null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix
open import Data.Matrix.HelperTheorems
open import Data.Matrix.RingProperties


import NFA
open module nfalib = NFA ⅀ _≟_


consnd18 : (nfa1 nfa2 : NFA)(x : ⅀)(st : 1 × _)
  → st ⋆ (F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x) ⋆ F nfa2 ≡ [ [ true ] ]
  → st ⋆ F nfa1 ≡ [ [ true ] ]
consnd18 nfa1 nfa2 x sty p rewrite 
  mlaw5 (F nfa1) (I nfa2) (δ nfa2 x)
  | sym (mlaw5  (sty) (F nfa1) (I nfa2 ⋆ δ nfa2 x))
  | mlaw5  (sty ⋆ F nfa1) (I nfa2 ⋆ δ nfa2 x)
   (F nfa2)
  = ht111 (sty ⋆ F nfa1) (I nfa2 ⋆ δ nfa2 x ⋆ F nfa2) p

ht21 : (nfa1 nfa2 : NFA)(x : ⅀)
  → (F nfa1 ⋆ I nfa2 ++ id) ⋆ δ nfa2 x 
    ≡ (F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++ δ nfa2 x 
ht21 nfa1 nfa2 x
  rewrite concatsup12 (F nfa1 ⋆ I nfa2) (id) (δ nfa2 x) 
  | idlaws (δ nfa2 x) = refl


consnd15 : (nfa : NFA)(sty' : 1 × (∇ nfa))(xs : String)
  → (run nfa xs (null {1} {_}) ⋆ F nfa) ≡ [ [ false  ] ]
consnd15 nfa sty' [] = mlaw7op {∇ nfa} {1} (F nfa)
consnd15 nfa sty' (x :: xs) rewrite (mlaw7op {_} {1} (δ nfa x)) = consnd15 nfa (replicate false ∷ []) xs


consnd16 : (k : ℕ)
  → (zipWith _∨_ (replicate {_} {k} false) (replicate false) ∷ []) ≡ (replicate false ∷ [])
consnd16 nzero = refl
consnd16 (suc n) = cong (λ q → q ∷ []) (cong (_∷_ false) (cong (λ q → head q) (consnd16 n)))


consnd17 : (nfa1 nfa2 : NFA)(sty : 1 × _)(x : ⅀)
  → sty ⋆ (F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x) ⋆ F nfa2
    ≡ [ [ true ] ]
  → (I nfa2 ⋆ δ nfa2 x ⋆ F nfa2) ≡ [ [ true ] ]
consnd17 nfa1 nfa2 sty x p rewrite 
  mlaw5  (F nfa1) (I nfa2) (δ nfa2 x)
  | sym (mlaw5 sty (F nfa1) (I nfa2 ⋆ δ nfa2 x))
  | mlaw5  (sty ⋆ F nfa1) (I nfa2 ⋆ δ nfa2 x) (F nfa2)
  = ht121 (sty ⋆ F nfa1) (I nfa2 ⋆ δ nfa2 x ⋆ F nfa2) p


ht23 : (nfa1 nfa2 : NFA)
  → I nfa1 ⋆ (F nfa1 ⋆ (I nfa2 ⋆ F nfa2)) ≡ [ [ true ] ]
  → I nfa1 ⋆ F nfa1 ≡ [ [ true ] ]
ht23 nfa1 nfa2 p rewrite 
  sym (mlaw5 (I nfa1) (F nfa1) (I nfa2 ⋆ F nfa2)) 
  = ht111 (I nfa1 ⋆ F nfa1) (I nfa2 ⋆ F nfa2) p



ht24 : (nfa1 nfa2 : NFA)
  → I nfa1 ⋆ (F nfa1 ⋆ (I nfa2 ⋆ F nfa2)) ≡ [ [ true ] ]
  → I nfa2 ⋆ F nfa2 ≡ [ [ true ] ]
ht24 nfa1 nfa2 p rewrite 
  sym (mlaw5 (I nfa1) (F nfa1) (I nfa2 ⋆ F nfa2)) 
  = ht121 _ _ p


{- cannot be directly substituted into proof -}
consnd21 : (nfa1 nfa2 : NFA)(xs : String)
  → run (nfa1 ○′ nfa2) xs (I nfa1 ++++ null) ≡
    take' (∇ nfa1) (run (nfa1 ○′ nfa2) xs (I nfa1 ++++ null))
    ++++
    init' {∇ nfa1} (run (nfa1 ○′ nfa2) xs (I nfa1 ++++ null))
consnd21 nfa1 nfa2 xs = takeinit {∇ nfa1} (run (nfa1 ○′ nfa2) xs (I nfa1 ++++ null))





consnd22 : (nfa1 nfa2 : NFA)(xs : String)(sty : 1 × (∇ nfa1))(sty' : 1 × (∇ nfa2))
  → take' (∇ nfa1) (run (nfa1 ○′ nfa2) xs (sty ++++ sty')) 
          ≡ run nfa1 xs sty
consnd22 nfa1 nfa2 [] sty sty' = htmain221 {∇ nfa1} sty sty'
consnd22 nfa1 nfa2 (x :: xs) sty sty' rewrite
  concatsup11
    (zipWith _++_ sty sty')
    (δ nfa1 x ++ replicate (replicate false))
    ((F nfa1 ⋆ I nfa2 ++ id) ⋆
         δ nfa2 x)
  | con-⊗-stack sty sty' (δ nfa1 x) (null)
  | mlaw7 {_} {_} {∇ nfa1} sty'
  | mlaw6 (sty ⋆ δ nfa1 x) 
  = consnd22 nfa1 nfa2 xs (sty ⋆ δ nfa1 x) 
    ((sty ++++ sty')
      ⋆ ((F nfa1 ⋆ I nfa2 ++ id) ⋆ δ nfa2 x))
  


consnd2 : (nfa₁ nfa₂ : NFA) → (u : String)
  → (run nfa₁ u (I nfa₁)) ⋆ F nfa₁ ≡ null
  → (run (nfa₁ ○′ nfa₂) u  ⟦ I nfa₁ ∣ null ⟧) ⋆ ⟦ F nfa₁ / F nfa₂ ⟧ ≡ 
    (run (nfa₁ ○′ nfa₂) u  ⟦ I nfa₁ ∣ null ⟧) ⋆ ⟦ null {∇ nfa₁} / F nfa₂ ⟧
consnd2 nfa₁ nfa₂ [] p 
  rewrite con-⊗-stack  (I nfa₁) (null {1} {∇ nfa₂}) (F nfa₁) (F nfa₂)
  | con-⊗-stack  (I nfa₁) (null {1} {∇ nfa₂})(null {∇ nfa₁} {1})
    (F nfa₂)
  | p 
  | mlaw7 {_} {_} {1} (I nfa₁) = refl
consnd2 nfa₁ nfa₂ xs p = trans (cong (λ q → q ⋆ (F nfa₁ ++ F nfa₂)) (consnd21 nfa₁ nfa₂ xs)) (trans (con-⊗-stack 
  (take' (∇ nfa₁) (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)))
  (init' {∇ nfa₁} (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)))
  (F nfa₁)
  (F nfa₂)) (trans (cong (λ q → q ⊹ (init' {∇ nfa₁}
       (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)) ⋆ F nfa₂)) (cong (λ q → q ⋆ F nfa₁) (consnd22 nfa₁ nfa₂ xs (I nfa₁) (replicate {_} {∇ nfa₂} false ∷ [])))) (trans (htmain23 
  (run nfa₁ xs (I nfa₁)) (F nfa₁) (replicate (false ∷ [])) (init' {∇ nfa₁}
       (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)) ⋆ F nfa₂) p (mlaw7 {_} {_} {1} (run nfa₁ xs (I nfa₁)))) (trans (cong (λ q → q ⊹ (init' {∇ nfa₁}
       (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)) ⋆ F nfa₂)) (cong (λ q → q ⋆ replicate (false ∷ [])) (sym (consnd22 nfa₁ nfa₂ xs (I nfa₁) (replicate {_} {∇ nfa₂} false ∷ []))))) (trans (sym (con-⊗-stack 
  (take' (∇ nfa₁) (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)))
  (init' {∇ nfa₁} (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null)))
  (replicate (false ∷ []))
  (F nfa₂))) (trans (cong (λ q → q ⋆ (replicate {_} {∇ nfa₁} (false ∷ []) ++ (F nfa₂))) (sym (takeinit {∇ nfa₁} {∇ nfa₂}
  (run (nfa₁ ○′ nfa₂) xs (I nfa₁ ++++ null))))) refl))))))
 



consnd12 : (nfa1 nfa2 : NFA)(x : ⅀)(sty : 1 × _)
  → (sty ⋆ F nfa1) ≡ [ [ false ] ]
  → sty ++++ (null {1}) ⋆
       (δ nfa1 x ++ replicate (replicate false)) ++++
        ((F nfa1 ⋆ I nfa2 ++ id) ⋆
         δ nfa2 x) ≡ (sty ⋆ δ nfa1 x) ++++ (null {1})
consnd12 nfa1 nfa2 x sty prf 
  rewrite concatsup11 
      (zipWith _++_ sty (replicate false ∷ []))
      (δ nfa1 x ++ replicate (replicate false))
      ((F nfa1 ⋆ I nfa2 ++ id) ⋆ δ nfa2 x)
  | con-⊗-stack
      sty
      (replicate {_} {∇ nfa2} false ∷ [])
      (δ nfa1 x)
      (replicate (replicate false))
 | ht21 nfa1 nfa2 x
 | con-⊗-stack 
      sty
      (replicate {_} {∇ nfa2} false ∷ [])
      (F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x)
      (δ nfa2 x) 
 | mlaw7 {_} {1} {∇ nfa1} (replicate {_} {∇ nfa2} false ∷ [])
 | mlaw6 (sty ⋆ δ nfa1 x)
 | mlaw7op {_} {1} (δ nfa2 x) 
 | mlaw6 (sty ⋆ (F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x))
 | mlaw5 
   (F nfa1)
   (I nfa2)
   (δ nfa2 x)
 | sym (mlaw5
       sty
       (F nfa1)
       (I nfa2 ⋆ δ nfa2 x))
 | prf 
 | mlaw7op {1} {1}  (I nfa2 ⋆ δ nfa2 x) = refl


consnd13 : (nfa1 nfa2 : NFA)(x : ⅀)(sty : 1 × _)
  → sty ⋆ F nfa1 ≡ [ [ true ] ]
  → (sty ⋆ (F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x)) ≡ I nfa2 ⋆ δ nfa2 x
consnd13 nfa1 nfa2 x sty p 
  rewrite mlaw5 
   (F nfa1)
   (I nfa2)
   (δ nfa2 x)
 | sym (mlaw5
   sty
   (F nfa1)
   (I nfa2 ⋆ δ nfa2 x))
 | p
 | mlaw7op {1} {1}  (I nfa2 ⋆ δ nfa2 x) 
 | idlaws (I nfa2 ⋆ δ nfa2 x) = refl


ht22 : {k l : ℕ}(x' : ⅀)(st1 : 1 × k)(st2 : 1 × l)(st3 : _ × _)
  → (m1 : k × k)(m2 : k × 1)(m3 : 1 × l)(m4 : l × l)
  → (st1 ++++ (st3 ⊹ st2) ⋆ (m1 ++ (null {l})) ++++ ((m2 ⋆ m3 ++ id) ⋆ m4)) 
     ≡ 
    (st1 ⋆  m1) ++++  ((st1 ⋆ m2 ⋆ m3 ⋆ m4) ⊹  (st3 ⋆ m4) ⊹ (st2 ⋆ m4))
ht22 {k} {l} x' st1 st2 st3 m1 m2 m3 m4 
  rewrite concatsup11  (st1 ++++ (st3 ⊹ st2)) (m1 ++ (null {l})) ((m2 ⋆ m3 ++ id) ⋆ m4)
  | con-⊗-stack st1 (st3 ⊹ st2) m1 (null {l}) 
  | mlaw7 {_} {_} {k} (st3 ⊹ st2) 
  | mlaw6 (st1 ⋆ m1)
  | concatsup12 (m2 ⋆ m3) id m4
  | idlaws m4
  | con-⊗-stack st1 (st3 ⊹ st2) (m2 ⋆ m3 ⋆ m4) m4
  | mlaw9 st3 st2 m4
  | mlaw5 m2 m3 m4
  | sym (mlaw5 st1 m2 (m3 ⋆ m4)) 
  | sym (mlaw5 (st1 ⋆ m2) m3 m4)
  | sym (mlaw3 (st1 ⋆ m2 ⋆ m3) (st3 ⋆ m4) (st2 ⋆ m4)) 
  | mlaw3 (st1 ⋆ m2 ⋆ m3 ⋆ m4) (st3 ⋆ m4) (st2 ⋆ m4) = refl


consnd11 : (nfa1 nfa2 : NFA)(x : ⅀)(xs : String)(sty : 1 × (∇ nfa1))(sty' : 1 × (∇ nfa2))(sty'' sty''' : 1 × (∇ nfa2))
  → run nfa2 xs sty' ⋆ F nfa2 ≡ [ [ false ] ]
  → run nfa2 xs sty'' ⋆ F nfa2 ≡ [ [ false ] ]
  → run (nfa1 ○′ nfa2) xs (sty ++++ (sty''' ⊹ sty')) ⋆ (null {(∇ nfa1)} {1} ++ F nfa2)
       ≡ 
    run (nfa1 ○′ nfa2) xs (sty ++++ (sty''' ⊹ sty'')) ⋆ (replicate {_} {∇ nfa1} (false ∷ []) ++ F nfa2)

consnd11 nfa1 nfa2 x [] st st' st'' st''' p1 p2 
  rewrite con-⊗-stack st (st''' ⊹ st') (null {(∇ nfa1)} {1}) (F nfa2)
  | con-⊗-stack  st (st''' ⊹ st'') (null {∇ nfa1} {1}) (F nfa2) 
  | mlaw1 st''' st' (F nfa2)
  | mlaw1 st''' st'' (F nfa2)
  | p1 
  | p2 = refl
consnd11 nfa1 nfa2 x (x' :: xs) st st' st'' st''' p1 p2 
 rewrite ht22 x' st st'' st''' (δ nfa1 x') (F nfa1) (I nfa2) (δ nfa2 x') 
 | ht22 x' st st' st''' (δ nfa1 x') (F nfa1) (I nfa2) (δ nfa2 x') 
 | consnd11 nfa1 nfa2 x xs (st ⋆ δ nfa1 x') 
    (st' ⋆ δ nfa2 x') 
    (st'' ⋆ δ nfa2 x') 
    ((st ⋆ F nfa1 ⋆ I nfa2 ⋆ δ nfa2 x') ⊹ (st''' ⋆ δ nfa2 x')) p1 p2 
 = refl


consnd14 : (nfa1 nfa2 : NFA)(xs : String)(sty : 1 × (∇ nfa1))(sty' : 1 × (∇ nfa2))
  → 
  run (nfa1 ○′ nfa2) xs (sty ++++ sty')⋆ (null {∇ nfa1} ++ F nfa2)
  ≡ 
  run (nfa1 ○′ nfa2) xs (sty ++++ (null ⊹ sty')) ⋆ (null {(∇ nfa1)} {1} ++ F nfa2)
consnd14 y y' xs sty sty' rewrite 
  mlaw6op sty' = refl



cons-split-state : (x : ⅀)(u : String)(nfa₁ nfa₂ : NFA)(st : 1 × _)
  →  run (nfa₁ ○′ nfa₂) (x :: u) ⟦ st ∣ null ⟧
      ⋆  ⟦ (null {∇ nfa₁}) / F nfa₂ ⟧ ≡ id {1}
  → Σ[ v ∈ String ] Σ[ w ∈ String ] (x :: u) ≡ v +++ w
    ⊗ run nfa₁ v st ⋆ F nfa₁ ≡ id {1}
    ⊗ run nfa₂ w (I nfa₂) ⋆ F nfa₂ ≡ id {1}
cons-split-state x [] nfa₁ nfa₂ sty p
  rewrite concatsup11 
    (zipWith _++_ sty (replicate false ∷ []))
    (δ nfa₁ x ++ replicate (replicate false))
    ((F nfa₁ ⋆ I nfa₂ ++ id) ⋆ δ nfa₂ x)
  | con-⊗-stack 
    sty
    (replicate {_} {∇ nfa₂} false ∷ [])
    (δ nfa₁ x)
    (replicate (replicate false))
  | ht21 nfa₁ nfa₂ x 
  | con-⊗-stack 
    sty
    (replicate {_} {∇ nfa₂} false ∷ [])
    (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x)
    (δ nfa₂ x)
  | mlaw7 {∇ nfa₂} {1} {∇ nfa₁} (replicate {_} {∇ nfa₂} false ∷ [])
  | mlaw7op {_} {1} (δ nfa₂ x)
  | mlaw6 (sty ⋆ δ nfa₁ x)
  | mlaw6 ((sty ⋆
        (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x))) 
  | con-⊗-stack 
    (sty ⋆ δ nfa₁ x)
    (sty ⋆
        (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x))
    (replicate (false ∷ []))
    (F nfa₂)
  | mlaw7 {∇ nfa₁} {1} {1} (sty ⋆ δ nfa₁ x) 
  | mlaw6op (sty ⋆
       (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x)
       ⋆ F nfa₂) = [] , x :: [] , refl , consnd18 nfa₁ nfa₂ x sty p  , consnd17 nfa₁ nfa₂ sty x p
cons-split-state x (x' :: xs) nfa₁ nfa₂ sty p 
  with inspect' (sty ⋆ F nfa₁)
cons-split-state x (x' :: xs) nfa₁ nfa₂ sty p | it ((false ∷ []) ∷ []) prf1
  rewrite consnd12 nfa₁ nfa₂ x sty prf1
  with cons-split-state x' xs nfa₁ nfa₂ (sty ⋆ δ nfa₁ x) p 
... | d1 , d2 , d3 , d4 , d5 = x :: d1 , d2 , trans (cong (λ q → x :: q) d3) refl , d4 , d5 -- `easy`
cons-split-state x (x' :: xs) nfa₁ nfa₂ sty p | it ((true ∷ []) ∷ []) prf1
  with inspect' (runNFA nfa₂ (x :: x' :: xs))
... | it ((true ∷ []) ∷ []) prf2 = [] , x :: x' :: xs , refl , prf1 , prf2
... | it ((false ∷ []) ∷ []) prf2 rewrite 
  concatsup11 
    (zipWith _++_ sty (replicate false ∷ []))
    (δ nfa₁ x ++ replicate (replicate false))
    ((F nfa₁ ⋆ I nfa₂ ++ id) ⋆
       δ nfa₂ x)
  | con-⊗-stack 
    sty
    (replicate {_} {∇ nfa₂} false ∷ [])
    (δ nfa₁ x)
    (replicate (replicate false))
  | ht21 nfa₁ nfa₂ x
  | con-⊗-stack 
    sty
    (replicate {_} {∇ nfa₂} false ∷ [])
    (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x)
    (δ nfa₂ x)
  | mlaw7 {∇ nfa₂} {1} {∇ nfa₁} (replicate {_} {∇ nfa₂} false ∷ [])
  | mlaw7op {_} {1} (δ nfa₂ x)
  | mlaw6 (sty ⋆ δ nfa₁ x)
  | mlaw6 ((sty ⋆
        (F nfa₁ ⋆ I nfa₂ ⋆ δ nfa₂ x)))
  | consnd13 nfa₁ nfa₂ x sty prf1
  | consnd14 nfa₁ nfa₂ (x' :: xs) (sty ⋆ δ nfa₁ x) (I nfa₂ ⋆ δ nfa₂ x)  
  | consnd11 nfa₁ nfa₂ x (x' :: xs) (sty ⋆ δ nfa₁ x) (I nfa₂ ⋆ δ nfa₂ x) (replicate false ∷ []) (replicate false ∷ []) prf2 (consnd15 nfa₂ (I nfa₂ ⋆ δ nfa₂ x) (x' :: xs))
  | consnd16 (∇ nfa₂)
   with cons-split-state x' xs nfa₁ nfa₂ (sty ⋆ δ nfa₁ x) p
... | d1 , d2 , d3 , d4 , d5 =  x :: d1 , d2 , trans (cong (λ q → x :: q) d3) refl , d4 , d5



cons-split : (u : String) → (nfa₁ nfa₂ : NFA) → (st : 1 × (∇ nfa₁))
  → run (nfa₁ ○′ nfa₂) u  ⟦ (I nfa₁) ∣ null ⟧
      ⋆ ⟦ F nfa₁ ⋆ (I nfa₂ ⋆ F nfa₂) / F nfa₂ ⟧  ≡ id {1}
  → Σ[ v ∈ String ] Σ[ w ∈ String ] u ≡ v +++ w
    ⊗ run nfa₁ v (I nfa₁) ⋆ F nfa₁ ≡ id {1}
    ⊗ run nfa₂ w (I nfa₂) ⋆ F nfa₂ ≡ id {1}
cons-split [] nfa1 nfa2 sty p 
  rewrite con-⊗-stack 
    (I nfa1)
    (null {1})
    (F nfa1 ⋆ (I nfa2 ⋆ F nfa2))
    (F nfa2)
  | mlaw7op {_} {1} (F nfa2)
  | mlaw6 ((I nfa1 ⋆
       (F nfa1 ⋆ (I nfa2 ⋆ F nfa2)))) 
    = [] , [] , refl , ht23 nfa1 nfa2 p , ht24 nfa1 nfa2 p

cons-split (x :: xs) nfa1 nfa2 sty p with  inspect' (I nfa2 ⋆ F nfa2)

cons-split (x :: xs) nfa1 nfa2 sty p | it ((true ∷ []) ∷ []) prf 
 with (inspect' (runNFA nfa1  (x :: xs))) 
... | it ((false ∷ []) ∷ []) prf1 
  rewrite prf
  | idlaw (F nfa1)
  | consnd2 nfa1 nfa2 (x :: xs) prf1 = cons-split-state x xs nfa1 nfa2 (I nfa1) p 
... | it ((true ∷ []) ∷ []) prf1 = (x :: xs) , [] , sym (nulllist (x :: xs)) , prf1 , prf

cons-split (x :: xs) nfa1 nfa2 sty p | it ((false ∷ []) ∷ []) prf 
 rewrite prf | mlaw7 {1} {∇ nfa1} {1} (F nfa1) = cons-split-state x xs nfa1 nfa2 (I nfa1) p



ht23' : {k l : ℕ}(Infa1  : 1 × k)(Fnfa1  : k × 1)(Infa2 : 1 × l)(Fnfa2 : l × 1)
  → Infa1 ⋆ (Fnfa1 ⋆ (Infa2 ⋆ Fnfa2)) ≡ [ [ true ] ]
  → Infa1 ⋆ Fnfa1 ≡ [ [ true ] ]
ht23' Infa1 Fnfa1 Infa2 Fnfa2 p rewrite 
  sym (mlaw5 (Infa1) (Fnfa1) (Infa2 ⋆ Fnfa2)) 
  = ht111 (Infa1 ⋆ Fnfa1) (Infa2 ⋆ Fnfa2) p


ht24' : {k l : ℕ}(Infa1  : 1 × k)(Fnfa1  : k × 1)(Infa2 : 1 × l)(Fnfa2 : l × 1)
  → Infa1 ⋆ (Fnfa1 ⋆ (Infa2 ⋆ Fnfa2)) ≡ [ [ true ] ]
  → Infa2 ⋆ Fnfa2 ≡ [ [ true ] ]
ht24' Infa1 Fnfa1 Infa2 Fnfa2 p rewrite 
  sym (mlaw5 (Infa1) (Fnfa1) (Infa2 ⋆ Fnfa2)) 
  = ht121 _ _ p

