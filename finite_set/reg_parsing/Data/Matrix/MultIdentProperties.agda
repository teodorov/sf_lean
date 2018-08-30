
open import Algebra.CommSemiRings

module Data.Matrix.MultIdentProperties where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr

import Data.Matrix; open Data.Matrix
import Data.Matrix.MultZeroProperties; open Data.Matrix.MultZeroProperties
import Data.Matrix.TransposeProperties; open Data.Matrix.TransposeProperties



{- PROPERTY: m*one = m -}

m-one*0 : {n m : ℕ}(xs : Vec R m)(vs : m × (suc n)) →   
 multRow (one ∷ zero ∷ replicate zero) (zipWith _∷_ xs vs) ≡ xs
m-one*0 [] [] = refl
m-one*0 {n} (x ∷ xs) (y ∷ ys) rewrite 
 m-zero*4 y  | m-zero*3 {n} {zero} | law3 {x} = cong (_∷_ x) (m-one*0 _ ys)


m-one*1 : {n m : ℕ}(x : Vec R m)(xs : n × m) 
  → multRow (one ∷ replicate zero) (zipWith _∷_ x (〈 xs 〉)) ≡ x
m-one*1 [] [] = refl
m-one*1 [] ([] ∷ xs) with (zipWith _∷_ [] (zipWith _∷_ [] (〈 xs 〉)))
m-one*1  [] ([] ∷ xs) | [] = refl
m-one*1 (x ∷ xs) [] rewrite  law3 {x} = cong (_∷_ x) (m-one*1 xs [])
m-one*1 {suc n} {suc m} (x ∷ xs) (x' ∷ xs') with  (zipWith _∷_ x' (〈 xs' 〉))
... | v ∷ vs rewrite  m-zero*4 v  | m-zero*3 {n} {zero}  | law3 {x} = cong (_∷_ x) (m-one*0 xs vs) 


m-one*3 : {n : ℕ}(xs : Vec R n) →  multRow (zero ∷ []) (zipWith _∷_ xs (replicate [])) ≡ replicate zero
m-one*3 [] = refl
m-one*3 (x ∷ xs)  = cong (_∷_ _) (m-one*3 xs)

m-one*4 : {n m : ℕ}(xs : Vec R n)(ys : Vec R m)(yss : m × n) 
  → multRow (zero ∷ xs) (zipWith _∷_ ys yss) ≡ multRow xs yss
m-one*4 xs [] [] = refl
m-one*4 (xs) (y ∷ ys) (zs ∷ zss) 
          = cong (_∷_ _) (m-one*4 xs ys zss)


m-one*2 : {n m k : ℕ}(xs : Vec R k)(vss : m × n)(xss : n × k) 
  → multiply (zipWith _∷_ (replicate zero) vss) (xs ∷ xss) ≡ multiply vss xss
m-one*2 xs [] yss = refl
m-one*2 {nzero} {suc m} {k} xs ([] ∷ vss) [] rewrite m-zero*1 {k} | m-one*3 {k} xs = cong (_∷_ _) (m-one*2 xs vss [])
m-one*2 {suc n} {suc m} {k} xs (vs ∷ vss) (ys ∷ yss) 
  rewrite m-one*4 {suc n} {k} (vs) (xs) ((zipWith _∷_ ys (〈 yss 〉))) 
    = cong (_∷_ _) (m-one*2 xs vss (ys ∷ yss))


m-one* : {n m : ℕ}(xss : m × n)
  →  multiply (id {m}) xss ≡ xss
m-one* [] = refl
m-one* {n} {suc m} (xs ∷ xss) 
  rewrite m-one*1 {m} {n} xs xss | m-one*2 {m} {m} {n} xs (id {m} ) xss = cong (_∷_ _) (m-one* xss)
--cong (_∷_ _) (m-one* xss)


{- PROPERTY: one*m = m -}

m-*one2 : {n : ℕ}(xs : Vec R n) 
  → (zipWith _*_ xs (replicate zero)) ≡ replicate zero
m-*one2 [] = refl
m-*one2 (x ∷ xs) rewrite law11 {x} = cong (_∷_ _) (m-*one2 xs)


m-*one3 : {n m : ℕ}(x : R)(xs : Vec R n)(vss : m × n)
  → multRow (x ∷ xs) (zipWith _∷_ (replicate zero) vss) 
            ≡  multRow xs vss
m-*one3 {nzero} x [] [] = refl
m-*one3 {nzero} x [] ([] ∷ xs) rewrite law11 {x}  = cong (_∷_ _) (m-*one3 x [] xs)
m-*one3 x (x' ∷ xs) [] = refl
m-*one3 x (x' ∷ xs) (x0 ∷ xs') rewrite law11 {x}  = cong (_∷_ _) (m-*one3 x (x' ∷ xs) xs')


m-*one0 :{n : ℕ}(xs : Vec R n) → multRow xs id ≡ xs
m-*one0 [] = refl
m-*one0 {suc n} (x ∷ xs) rewrite law7 {x} | m-zero*4 {n} xs | m-*one2 {n} xs | m-zero*3 {n} {zero} | law3 {x} | m-*one3 {n} {n} x xs (id)  = cong (_∷_ _) (m-*one0 xs)
--cong (_∷_ _) (m-*one0 xs)


m-*one1 :{n : ℕ} →  〈 (id {n}) 〉 ≡ id {n}
m-*one1 {nzero} = refl
m-*one1 {suc n}  rewrite m-TT1 {n} {n} (id) (replicate zero) | m-*one1 {n} = cong (_∷_ _) refl
--cong (_∷_ _) refl


m-*one : {n m : ℕ}(xss : m × n)
  →  multiply xss (id {n}) ≡ xss
m-*one [] = refl
m-*one {n} {suc m}  (x ∷ xs) 
  rewrite m-*one1 {n} | m-*one0 {n} x = cong (_∷_ _) (m-*one xs)

