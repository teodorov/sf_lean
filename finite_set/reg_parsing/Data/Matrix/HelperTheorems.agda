
open import Algebra.CommSemiRings

module Data.Matrix.HelperTheorems where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Algebra.Logic
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Matrix
open import Data.Matrix.RingProperties

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr


htmain2211 : {k l : ℕ}(a c : Vec Bool k)(b d : Vec Bool l)
 → (a ++ b) ≡ (c ++ d)
 → (a ≡ c)
htmain2211 [] [] b d p = refl
htmain2211 (true ∷ xs) (true ∷ ys) xs' ys' p = cong (_∷_ _) (htmain2211 xs ys xs' ys' (cong (λ q → tail q) p))
htmain2211 (true ∷ xs) (false ∷ ys) xs' ys' ()
htmain2211 (false ∷ xs) (true ∷ ys) xs' ys' ()
htmain2211 (false ∷ xs) (false ∷ ys) xs' ys' p = cong (_∷_ _) (htmain2211 xs ys xs' ys' (cong (λ q → tail q) p))


-- make it more general
takeinit0 : {k n : ℕ}(ys : Vec Bool n)(zs : Vec Bool k)
 →  (take n (ys ++ zs)) ≡ ys
takeinit0 {_} {n} ys zs 
 with splitAt n (ys ++ zs)
... | (d1 , d2 , prf) rewrite prf = sym (htmain2211 ys d1 zs d2 prf)


takeinit : {l k : ℕ}(os : 1 × (l ✚ k)) → os ≡ (take' {k} l os) ++++ (init' {l} {k} os)
takeinit {nzero} (x ∷ []) = refl
takeinit {suc n} {k} (xs ∷ []) with splitAt (suc n) xs
takeinit {suc n} {k} (.(y ∷ ys ++ zs) ∷ []) | (y ∷ ys , zs , refl) 
 rewrite takeinit0 ys zs = refl

idlemma1 : {k l : ℕ}(m : k × l)
  → zipWith _++_ (replicate (zero ∷ [])) m
    ≡ zipWith _∷_ (replicate zero) m
idlemma1 [] = refl
idlemma1 (x ∷ xs) = cong (_∷_ _) (idlemma1 xs)

{- multiply ≡ _⋆_ -}





helper1 : {k : ℕ}(m1 : 1 × k)(m2 : k × 1)(m3 : k × k)
  → m1 ⋆ ((id ⊹ m2 ⋆ m1) ⋆ m3) ≡ m1 ⋆ m3
helper1 m1 m2 m3  rewrite mlaw1 id (m2 ⋆ m1) m3
  | idlaws m3 
  | mlaw2 m1 m3 (m2 ⋆ m1 ⋆ m3)
  | mlaw5 m2 m1 m3
  | sym (mlaw5 m1 m2 (m1 ⋆ m3)) with m1 ⋆ m2
... | (true ∷ []) ∷ [] rewrite
  idlaws (m1 ⋆ m3) = plusidempotence (m1 ⋆ m3)
... | (false ∷ []) ∷ [] rewrite 
  mlaw7op {1} {1} (m1 ⋆ m3) = mlaw6 (m1 ⋆ m3)


helper2 : {k l m n : ℕ}(m1 : k × l)(m3 : l × m)(m2 : l × n)(m4 : n × l)
  → (m1 ⋆ ((id ⊹ m2 ⋆ m4) ⋆ m3)) ≡ (m1 ⋆ m3) ⊹ (m1 ⋆ m2 ⋆ m4 ⋆ m3)
helper2 m1 m3 m2 m4 
  rewrite mlaw1 id (m2 ⋆ m4) m3
  | idlaws m3
  | mlaw2 m1 m3 (m2 ⋆ m4 ⋆ m3)
  | mlaw5 m2 m4 m3
  | sym (mlaw5 m1 m2 (m4 ⋆ m3))
  | sym (mlaw5 (m1 ⋆ m2) m4 m3) = refl



helper3 : {k : ℕ}(m1 : 1 × 1)(m2 : 1 × 1)
  → m1 ⋆ m2 ≡ [ [ true ] ]
  → m1 ≡ [ [ true ] ]
helper3 ((true ∷ []) ∷ []) m2 p = refl
helper3 ((false ∷ []) ∷ []) m2 p rewrite 
  mlaw7op {1} {1} m2 with p
... | ()

helper4 : {k : ℕ}(m1 : 1 × 1)(m2 : 1 × 1)
  → m1 ⋆ m2 ≡ [ [ true ] ]
  → m2 ≡ [ [ true ] ]
helper4 m1 ((true ∷ []) ∷ [])  p = refl
helper4 m1 ((false ∷ []) ∷ []) p rewrite 
  mlaw7 {1} {1} {1} m1 with p
... | () 


helper5 : {k : ℕ}(m1 : 1 × k)(m2 : k × 1)(m3 : 1 × k)(m4 : k × k)
  → m1 ⋆ ((id ⊹ m2 ⋆ m3) ⋆ m4) ⋆ m2 ≡ [ [ true ] ]
  → m1 ⋆ m4 ⋆ m2 ≡ [ [ false ] ]
  → m1 ⋆ m2 ≡ [ [ true ] ]
helper5 m1 m2 m3 m4 p1 p2 
  rewrite helper2 m1 m4 m2 m3
  | mlaw1 (m1 ⋆ m4) (m1 ⋆ m2 ⋆ m3 ⋆ m4) m2
  | p2
  | mlaw6op (m1 ⋆ m2 ⋆ m3 ⋆ m4 ⋆ m2)
    with inspect' (m1 ⋆ m2)
helper5 m1 m2 m3 m4 p1 p2 | it ((false ∷ []) ∷ []) prf1 
  rewrite mlaw5 (m1 ⋆ m2) m3 m4
  | mlaw5 (m1 ⋆ m2) (m3 ⋆ m4) m2 
  | prf1
  | mlaw7op {1} {1} (m3 ⋆ m4 ⋆ m2) with p1
... | ()
helper5 m1 m2 m3 m4 p1 p2 | it ((true ∷ []) ∷ []) prf1 
  rewrite mlaw5 (m1 ⋆ m2) m3 m4
  | mlaw5 (m1 ⋆ m2) (m3 ⋆ m4) m2
  | prf1 = refl

htmain23 : {k : ℕ}(a : 1 × k)(b d : k × 1)(c : 1 × 1)
  → a ⋆ b ≡ [ [ false ] ]
  → a ⋆ d ≡ [ [ false ] ]
  → a ⋆ b ⊹ c ≡ a ⋆ d ⊹ c
htmain23 a b d c p1 p2 rewrite p1 | p2 = refl

htmain221 : {k l : ℕ}(a : 1 × k)(b : 1 × l)
  → take' k (a ++++ b) ≡ a
htmain221 {nzero} ([] ∷ []) (x ∷ []) = refl
htmain221 {suc n} (xs ∷ []) (ys ∷ [])
  with splitAt (suc n) (xs ++ ys)
htmain221 {suc n} (_∷_  xs []) (_∷_ ys []) | d1 , d2 , prf rewrite prf = cong (λ q → q ∷ []) (sym (htmain2211 xs d1 ys d2 prf))
