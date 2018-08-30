
open import Algebra.CommSemiRings

module Data.Matrix.AdditionProperties where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality
open import Algebra.Logic
open import Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr


{- PROPERTY: a + b = b + a -}
m-+comm0 : {n : ℕ}(x y : Vec R n) 
  → zipWith _+_ x y ≡ zipWith _+_ y x
m-+comm0 [] [] = refl
m-+comm0 (x ∷ xs) (y ∷ ys) 
  rewrite law4 {x} {y} = cong (_∷_ _) (m-+comm0 xs ys)


m-+comm : {n m : ℕ}(m1 : m × n)(m2 : m × n) 
  → m1 ⊹ m2 ≡  m2 ⊹ m1
m-+comm [] [] = refl
m-+comm (x ∷ xs) (y ∷ ys) 
  rewrite m-+comm0 x y = cong (_∷_ _) (m-+comm xs ys)



{- PROPERTY: 0 + a = a -}
m-+zero0 : {n : ℕ}(v1 : Vec R n) 
  → zipWith _+_ (replicate zero) v1 ≡ v1
m-+zero0 [] = refl
m-+zero0 (x ∷ xs) = cong (_∷_ _) (m-+zero0 xs) 




m-+zero : {n m : ℕ}(xss : m × n) 
  → (null {m} {n}) ⊹ xss ≡ xss
m-+zero [] = refl
m-+zero (xs ∷ xss) = 
  trans 
        (cong (\ y → y ∷  (replicate (replicate zero)) ⊹ xss) (m-+zero0 xs)) 
        (cong (_∷_ _) (m-+zero xss))


{- PROPERTY: a + 0 = a -}
m-zero+ : {n m : ℕ}(xss : m × n)
  → xss ⊹ (null {m} {n}) ≡ xss
m-zero+ {n} {m} xss = trans (m-+comm xss (null {m} {n})) (m-+zero xss)


{- PROPERTY: matrix addition distributivity -}
m-+assoc0 :  {n : ℕ}(x y z : Vec R n) 
  → zipWith _+_ x (zipWith _+_ y z) ≡ zipWith _+_ (zipWith _+_ x y) z
m-+assoc0 [] [] [] = refl
m-+assoc0 (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite law1 {x} {y} {z} = 
  cong (_∷_ _) (m-+assoc0 {_} xs ys zs) 


m-+assoc : {n m : ℕ} → (m1 m2 m3 : m × n) 
  →  m1 ⊹ (m2 ⊹ m3) ≡ (m1 ⊹ m2) ⊹ m3
m-+assoc [] [] [] = refl
m-+assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite m-+assoc0 x y z = 
  cong (_∷_ _) (m-+assoc xs ys zs)
