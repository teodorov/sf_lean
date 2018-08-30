
open import Algebra.CommSemiRings

module Data.Matrix.AdditionProperties2  where

open import Data.Vec hiding (zipWith; map)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality
import Data.Matrix

open Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr

{- PROPERTY: a ⊹ b = b ⊹ a -}
⊹-comm0 : {n : ℕ}(x y : Vec R n) 
  → zipWith _+_ x y ≡ zipWith _+_ y x
⊹-comm0 [] [] = refl
⊹-comm0 (x ∷ xs) (y ∷ ys) 
  rewrite law4 {x} {y} 
  = cong (_∷_ _) (⊹-comm0 xs ys)

⊹-comm : {n m : ℕ}(m₁ : n × m)(m₂ : n × m) 
  → m₁ ⊹ m₂ ≡  m₂ ⊹ m₁
⊹-comm [] [] = refl
⊹-comm ([] ∷ xs) ([] ∷ ys) = cong (_∷_ []) (⊹-comm xs ys)
⊹-comm (x ∷ xs) (y ∷ ys)  rewrite ⊹-comm0 x y 
  = cong (_∷_ _) (⊹-comm xs ys)


{- PROPERTY: 0 ⊹ a = a -}
⊹-zero0 : {n : ℕ}(v1 : Vec R n) 
  → zipWith _+_ (replicate zero) v1 ≡ v1
⊹-zero0 [] = refl
⊹-zero0 (x ∷ xs) 
  = cong (_∷_ _) (⊹-zero0 xs) 


⊹-zerol : {k l : ℕ}(m : k × l) 
  → null ⊹ m ≡ m
⊹-zerol [] = refl
⊹-zerol (xs ∷ xss) = 
  trans 
        (cong (λ y → y ∷ null  ⊹ xss) 
          (⊹-zero0 xs)) 
        (cong (_∷_ _) (⊹-zerol xss))


{- PROPERTY: a ⊹ 0 = a -}
⊹-zeror : {k l : ℕ}(m : k × l)
  → m ⊹ null ≡ m
⊹-zeror {n} {m} xss = trans (⊹-comm xss null) (⊹-zerol xss)


{- PROPERTY: m1 ⊹ (m2 ⊹ m3) ≡ (m1 ⊹ m2) ⊹ m3 -}
⊹-assoc0 :  {n : ℕ}(x y z : Vec R n) 
  → zipWith _+_ x 
    (zipWith _+_ y z) ≡ 
  zipWith _+_ (zipWith _+_ x y) z
⊹-assoc0 [] [] [] = refl
⊹-assoc0 (x ∷ xs) (y ∷ ys) (z ∷ zs) 
  rewrite law1 {x} {y} {z} 
  = cong (_∷_ _) (⊹-assoc0 xs ys zs) 


⊹-assoc : {n m : ℕ} → (m₁ m₂ m₃ : n × m) 
  → m₁ ⊹ (m₂ ⊹ m₃) ≡ (m₁ ⊹ m₂) ⊹ m₃
⊹-assoc [] [] [] = refl
⊹-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) 
  rewrite ⊹-assoc0 x y z 
  = cong (_∷_ _) (⊹-assoc xs ys zs)
