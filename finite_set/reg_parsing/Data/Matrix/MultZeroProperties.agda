
open import Algebra.CommSemiRings

module Data.Matrix.MultZeroProperties  where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality
open import Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr




{- PROPERTY: 0 * m = 0 -}
m-zero*4 : {n : ℕ}(v : Vec R n) 
  → zipWith _*_ (replicate zero) v ≡ replicate zero
m-zero*4 [] = refl
m-zero*4 (x ∷ xs)  = cong (_∷_ zero) (m-zero*4 xs)



m-zero*1 : {m : ℕ} 
  →  multRow {nzero} {m} [] (replicate []) ≡ replicate zero
m-zero*1 {nzero} = refl
m-zero*1 {suc n} = cong (_∷_ zero) m-zero*1



m-zero*0 : {m k : ℕ} 
  → multiply {nzero} {m} {k} (replicate []) [] ≡ 
     replicate (replicate zero)
m-zero*0 {nzero} = refl
m-zero*0 {suc n} {k} rewrite m-zero*1 {k} = cong (_∷_ _) m-zero*0


m-zero*3 : {n : ℕ}{x : R} 
  → (foldr (\ _ → R) _+_ x (replicate {_} {n} zero)) ≡ x
m-zero*3 {nzero} = refl
m-zero*3 {suc n} {x} 
--  rewrite law2 {foldr (λ _ → R) _+_ x (replicate {_} {n}  zero)} 
    = m-zero*3 {n}



m-zero*2 : {n m : ℕ}(xss : n × m) 
  → multRow (replicate zero) xss ≡ replicate zero
m-zero*2 [] = refl
m-zero*2 {suc n} {m} (x' ∷ xs') 
  rewrite m-zero*4 {m} x' | m-zero*3 {m} {zero} 
    = cong (_∷_ _) (m-zero*2 xs')



m-zero* : {n m k : ℕ}(xss : n × k)
  →  multiply (null {m} {n}) xss ≡ null {m} {k}
m-zero* {nzero} {m} {k} [] = m-zero*0
m-zero* {suc n} {nzero} (x ∷ xs) = refl
m-zero* {suc n} {suc m} {k} (x ∷ xs)
  rewrite m-zero*2 {k} {suc n} (zipWith _∷_ x (〈 xs 〉)) 
    = cong (_∷_ _) (m-zero* (x ∷ xs))


{- PROPERTY: m * 0 = 0  -}
m-*zero01 : {n m : ℕ} 
     → zipWith _∷_ (replicate {_} {n} zero) 
         (replicate (zero ∷ (replicate {_} {m} zero))) ≡ 
       replicate (zero ∷ zero ∷ replicate zero)
m-*zero01 {nzero} = refl
m-*zero01 {suc n} = cong (_∷_ _) m-*zero01


m-*zero0 : {n m : ℕ}  
  → (zipWith _∷_ 
             (zero ∷ replicate zero) 
             (〈 replicate (zero ∷ replicate zero ) 〉)) ≡ 
    null {suc m} {suc n} 
m-*zero0 {nzero} {nzero} = refl
m-*zero0 {nzero} {suc n} = cong (_∷_ _) m-*zero0
m-*zero0 {suc n} {nzero} rewrite m-*zero0 {n} {nzero} = refl
m-*zero0 {suc n} {suc m}  
  rewrite m-*zero0 {n} {suc m} | m-*zero01 {m} {n} = refl


m-*zero1 : {n : ℕ}(v : Vec R n) 
  → zipWith _*_ v (replicate zero)  ≡ replicate zero
m-*zero1 [] = refl
m-*zero1 (x ∷ xs) 
  rewrite law11 {x} = cong (_∷_ _) (m-*zero1 xs)


m-*zero2 : {n : ℕ}{x : R} 
  → (foldr (\ _ → R) _+_ x (replicate {_} {n} zero)) ≡ x
m-*zero2 {nzero} = refl
m-*zero2 {suc n} {x} 
--  rewrite law2 {foldr (λ _ → R) _+_ x (replicate {_} {n}  zero)} 
    = m-*zero2 {n}



m-*zero3 : {n m : ℕ}(xs : Vec R (suc n)) 
  → multRow xs 
            (replicate {_} {m} (zero ∷ replicate {_} {n} zero)) ≡ 
    replicate {_} {m} zero
m-*zero3 {nzero} {nzero} (x ∷ []) = refl
m-*zero3 {nzero} {suc n} (x ∷ []) 
  rewrite law11 {x}  = cong (_∷_ _) (m-*zero3 (x ∷ []))
m-*zero3 {suc n} {nzero} (x ∷ xs) = refl
m-*zero3 {suc n} {suc n'} (x ∷ xs) 
  rewrite law11 {x} | 
    m-*zero1 {suc n} xs | 
    m-*zero2 {suc n}{zero}  = cong (_∷_ _) (m-*zero3 (x ∷ xs))



m-*zero4 : {m : ℕ} 
  →  multRow {nzero} {m} [] (replicate []) ≡ replicate zero
m-*zero4 {nzero} = refl
m-*zero4 {suc n} = cong (_∷_ zero) m-*zero4



m-*zero : {n m k : ℕ}(xss : m × n)
  →  multiply xss (null {n} {k}) ≡ null {m} {k}
m-*zero [] = refl
m-*zero {n} {suc m} {nzero} (x ∷ xs) 
  with 〈_〉 {nzero} {n} (replicate [])
... | [] = cong (_∷_ _) (m-*zero xs)
m-*zero {nzero} {suc m} {suc n'} ([] ∷ xs) 
  rewrite m-*zero4 {suc n'} = cong (_∷_ _) (m-*zero xs)
m-*zero {suc n} {suc m} {suc n'} (x ∷ xs) 
  rewrite m-*zero0 {n} {n'} | 
    m-*zero1 {suc n} (x) | 
    m-*zero2 {suc n}{zero} | 
    m-*zero3 {n} {n'} x = cong (_∷_ _) (m-*zero xs)

