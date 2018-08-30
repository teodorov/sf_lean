
open import Algebra.CommSemiRings

module Data.Matrix.TransposeProperties where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality

open import Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr



{- PROPERTY: transpose(transpose m) = m  -}
m-TT0 : ∀ {n}(m :  n × 0) 
  → replicate [] ≡ m

m-TT0 [] = refl
m-TT0 ([] ∷ xs) = cong (_∷_ _) (m-TT0 xs)

 
m-TT1 : ∀{m n}(xss : m × n)(xs : Vec R m) 
  → 〈 zipWith _∷_ xs xss 〉 ≡ xs ∷ 〈 xss 〉
m-TT1 [] [] = refl
m-TT1 (x ∷ xs) (x' ∷ xs') = 
  cong (zipWith _∷_ (x' ∷ x)) (m-TT1 xs xs')


m-TT : {l k : ℕ}(m : k × l) 
  → 〈 〈 m 〉 〉 ≡ m
m-TT {nzero} [] = refl
m-TT {suc n} [] = cong (zipWith _∷_ []) (m-TT {n} [])
m-TT (xs ∷ xss) =  
  trans (m-TT1 〈 xss 〉 xs) (cong (_∷_ _) (m-TT xss)) 
