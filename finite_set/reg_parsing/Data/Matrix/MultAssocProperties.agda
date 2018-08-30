
open import Algebra.CommSemiRings



module Data.Matrix.MultAssocProperties  where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr

import Data.Matrix; open Data.Matrix 
import Data.Matrix.TransposeProperties; open Data.Matrix.TransposeProperties

{- PROPERTY : (a * b) * c ≡ a * (b * c) -}

m-*assoc811 : (x x2 x' fs fr1 fr2 : R)
  → (x * ((x2  * x') + fr1)) + ((fs * x2) + fr2)
       ≡  (((x * x') + fs) * x2) + ((x * fr1) + fr2) 
m-*assoc811  x x2 x' fs fr1 fr2
  rewrite law8 {x} {x2 * x'} {fr1} | 
    law9 {x * x'} {fs} {x2} |
    law5 {x} {x'} {x2} |
    law12 {x'} {x2} |
    law1 {(x * (x2 * x'))} {(x * fr1)} {((fs * x2) + fr2)} |
    law1 {(x * (x2 * x'))} {(fs * x2)} {((x * fr1) + fr2)} |
    sym (law1 {(x * fr1)} {(fs * x2)} {fr2}) |
    law4 {(x * fr1)} {(fs * x2)} |
    law1 {fs * x2} {x * fr1} {fr2} = refl

m-*assoc01 : {n : ℕ}(x d : Vec R n)
  → (zipWith _*_ x d) ≡ (zipWith _*_ d x)
m-*assoc01 [] [] = refl
m-*assoc01 (x ∷ xs) (d ∷ ds) rewrite law12 {x} {d} = cong (_∷_ _) (m-*assoc01 xs ds)

m-*assoc3 : ∀{k n}(x1 : Vec R k)(xs1 : Vec (Vec R k) n)
  →  〈 (zipWith _∷_ x1 〈 xs1 〉) 〉 ≡ x1 ∷ xs1
m-*assoc3 xs ys rewrite m-TT (xs ∷ ys) = refl

m-*assoc04 : {n m : ℕ}(xs0 : Vec R n)(xs : n × m)
  → (〈 (zipWith _∷_ xs0 xs) 〉) ≡ xs0 ∷ 〈 xs 〉
m-*assoc04 [] [] = refl
m-*assoc04 (x ∷ xs) (x' ∷ xs') rewrite m-*assoc04 xs xs' = refl

m-*assoc02 : ∀{n m n'}(fs : Vec (Vec R n) (m))(ds : Vec (Vec R ( m)) n')
  (x : Vec R (m))
  → (zipWith _∷_
      (map
       (λ x0 → foldr _ _+_ zero (zipWith _*_ x x0))
       ds)
      (ds ⋆ fs)
      ≡  ds ⋆ (zipWith _∷_ x fs))
m-*assoc02 [] [] x = refl
m-*assoc02 [] ([] ∷ xs) [] = cong (_∷_ _) (m-*assoc02 [] xs [])
m-*assoc02 (x ∷ xs) [] x' = refl
m-*assoc02 (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) rewrite m-*assoc04 xs0 xs | m-*assoc01 (x0 ∷ xs0) x' = cong (_∷_ _) (m-*assoc02 (x ∷ xs) xs' (x0 ∷ xs0))

m-*assoc03 : ∀{m n}(ds : Vec (Vec R ( m)) 0)(xs : Vec (Vec R ( n)) ( m))
  →  〈 ds ⋆ xs 〉 ≡ replicate []
m-*assoc03 [] [] = refl
m-*assoc03 [] (x ∷ xs') = refl 

m-*assoc06 : {m n : ℕ}(xs : n × m)
  → xs ⋆ (replicate []) ≡ replicate []
m-*assoc06 [] = refl
m-*assoc06 {nzero} {suc n} (x ∷ xs) = cong (_∷_ _) (m-*assoc06 xs)
m-*assoc06 {suc n} {suc n'} (x ∷ xs) 
  with (zipWith _∷_ [] (〈 replicate {_} {n} [] 〉)) 
... | [] = cong (_∷_ _) (m-*assoc06 xs )

m-*assoc05 : ∀{m n}(ds : Vec (Vec R ( m)) 0)(xs : Vec (Vec R ( n)) ( m))
 →  (〈 xs 〉 ⋆ 〈 ds 〉 ≡ replicate [])
m-*assoc05 {nzero} {n} [] [] rewrite m-*assoc06 (replicate {_} {n} []) = refl
m-*assoc05 [] (x ∷ xs) rewrite m-*assoc06 ((zipWith _∷_ x  〈 xs 〉)) = refl


m-*assoc071 : (n n' : ℕ)
  → zipWith {n'}  _∷_
      (map
       (λ x → foldr _ _+_ zero (zipWith _*_ [] x))
       (replicate []))
      (replicate (replicate {_} {n} zero))
      ≡ replicate (zero ∷ replicate {_} {n} zero)
m-*assoc071 nzero nzero = refl
m-*assoc071 nzero (suc n) = cong (_∷_ _) (m-*assoc071 nzero n)
m-*assoc071 (suc n) nzero = refl
m-*assoc071 (suc n) (suc n') = cong (_∷_ _) (m-*assoc071 (suc n) n')

m-*assoc07 : ∀{n n'}(xs : 0 × n')(ds : n × 0)
  → 〈 ds  ⋆ xs 〉 ≡ null {n'} {n}
m-*assoc07 xs [] = refl
m-*assoc07 {suc n} {nzero} [] ([] ∷ xs) 
  with zipWith _∷_ [] (〈 xs ⋆ [] 〉) 
... | [] = refl
m-*assoc07 {suc n} {suc n'} [] ([] ∷ xs) 
  rewrite m-*assoc07 {n} {suc n'} [] xs  = cong (_∷_ _) (m-*assoc071 n n')

m-*assoc081 : (n : ℕ)
  → (replicate {_} {n} []) ⋆ [] ≡ replicate []
m-*assoc081 nzero = refl
m-*assoc081 (suc n) = cong (_∷_ _) (m-*assoc081 n)

m-*assoc0821 : (n : ℕ)
  → map
       (λ x → foldr _ _+_ zero (zipWith _*_ [] x))
       (replicate []) ≡ replicate {_} {n} zero
m-*assoc0821 nzero = refl
m-*assoc0821 (suc n) = cong (_∷_ _) (m-*assoc0821 n)

m-*assoc082 : (n k : ℕ)
  → _⋆_ {nzero} {n} {k} (replicate {_} {n} []) [] ≡
      replicate (replicate zero)
m-*assoc082 nzero k = refl
m-*assoc082 (suc n) nzero = cong (_∷_ _) (m-*assoc082 n nzero)
m-*assoc082 (suc n) (suc n') rewrite m-*assoc0821 n' = cong (_∷_ _) (m-*assoc082 n (suc n'))

m-*assoc08 : ∀{n n'}(xs : 0 × n')(ds : n × 0)
  → _⋆_ 〈 xs 〉 〈 ds 〉 ≡ null {n'} {n}
m-*assoc08 [] [] = m-*assoc081 _
m-*assoc08 [] ([] ∷ xs) 
  with (zipWith _∷_ [] 〈 xs 〉) 
... | [] = m-*assoc082 _ _



m-*assoc0 : ∀{m n k} → (m1 : n × m)(m2 : m × k) 
  → (〈 _⋆_ m1 m2 〉) ≡ _⋆_ (〈 m2 〉) (〈 m1 〉)
m-*assoc0 {nzero} {nzero} {nzero} [] [] = refl
m-*assoc0 {nzero} {nzero} {suc n} [] [] = cong (_∷_ _) (m-*assoc0 [] [])
m-*assoc0 {suc m} {nzero} {nzero} [] ([] ∷ xs)
  with (zipWith _∷_ [] (〈 xs 〉)) 
... | [] = refl
m-*assoc0 {suc m} {nzero} {suc n} ds (xs) rewrite m-*assoc03  ds xs | m-*assoc05 ds xs = refl
m-*assoc0 {nzero} {suc n} {nzero} ([] ∷ xs) [] 
  with zipWith _∷_ [] (〈 _⋆_ xs [] 〉)
... | [] = refl
m-*assoc0 {nzero} {suc n} {suc n'} (xs) ds 
  rewrite m-*assoc07 ds xs | m-*assoc08 ds xs = refl
m-*assoc0 {suc m} {suc n} {nzero} (x ∷ xs) ([] ∷ xs')
  with (zipWith _∷_ [] (〈 xs' 〉)) 
... | [] with (zipWith _∷_ [] (〈 _⋆_ xs ([] ∷ xs' ) 〉)) 
... | [] = refl
m-*assoc0 {suc m} {suc n} {suc n'} (x ∷ xs) (x' ∷ xs') rewrite
  m-*assoc0 xs (x' ∷ xs') 
  with (zipWith _∷_ x' (〈 xs' 〉)) 
... | d ∷ ds rewrite m-*assoc3 x xs | m-TT xs | m-*assoc01 x d
  with (〈 xs 〉)
... | fs  = cong (_∷_ _) (m-*assoc02 fs ds x)

m-*assoc31 : {n : ℕ}(xs : n × 0) → replicate [] ≡ xs
m-*assoc31 [] = refl
m-*assoc31 ([] ∷ xs) = cong (_∷_ _) (m-*assoc31 xs)


m-*assoc32 :  ∀{k n}(x1 : Vec R k)(xs1 : Vec (Vec R k) n)
  →  (zipWith _∷_ x1 (〈 xs1 〉)) ≡ 〈 x1 ∷ xs1 〉
m-*assoc32 _ _ = refl



m-*assoc81 : ∀{k m}(x : R)
  (x' : Vec R ( k))(xs' : Vec (Vec R m) ( k))
  (xs : Vec R m)(d : Vec R ( k))
  → 
 
  (foldr _ _+_ zero
      (zipWith _*_
       (map
        (λ x1 →
           foldr _ _+_ zero (zipWith _*_ (x ∷ xs) x1))
        ((zipWith _∷_ x' xs')))
       d))
  ≡ 
  ((x *
       foldr _ _+_ zero (zipWith _*_  d x'))

  +  ((foldr _ _+_ zero
      (zipWith _*_
       (map
        (λ x1 →
           foldr _ _+_ zero (zipWith _*_ (xs) x1))
        ((xs')))
       d))))
m-*assoc81 x [] [] _ [] rewrite law11 {x} = refl
m-*assoc81 x (x' ∷ xs) (x0 ∷ xs') (xs0) (x2 ∷ xs1) 
  rewrite m-*assoc811 (x) (x2) (x')
  (foldr _ _+_  zero (zipWith _*_ (xs0) x0))
  (foldr _ _+_ zero (zipWith _*_ xs1 xs))
  (foldr _ _+_ zero
       (zipWith _*_
        (map
         (λ x3 →
            foldr _ _+_ zero (zipWith _*_ (xs0) x3))
         xs')
        xs1)) = cong (_+_ ((x ∧ x' ∨
       foldr (λ _ → Bool) _∨_ false (zipWith _∧_ xs0 x0))
      ∧ x2)) (m-*assoc81 x xs xs' xs0 xs1)


m-*assoc83 : (n : ℕ)(d : Vec R (n))
  →    foldr _ _+_ zero
      (zipWith _*_
       (
        map
        (λ x1 → foldr _ _+_ zero (zipWith _*_ [] x1))
        (replicate {_} {n} []))
       d) ≡ zero
m-*assoc83 nzero [] = refl
m-*assoc83 (suc n) (x ∷ xs) = m-*assoc83 n xs

m-*assoc8 : ∀{k m}(xs' : Vec (Vec R ( k)) m)
  (xs : Vec R m)(d : Vec R ( k))
  → (foldr _ _+_ zero
      (zipWith _*_ (xs)
       (map
        (λ x1 → foldr _ _+_ zero (zipWith _*_ d x1))
        (xs')))) 
  ≡
  (foldr _ _+_ zero
      (zipWith _*_
       (map
        (λ x1 →
           foldr _ _+_ zero (zipWith _*_ (xs) x1))
        ((〈 xs' 〉)))
       d))
m-*assoc8 {nzero} [] [] [] = refl
m-*assoc8 {suc n} [] [] d rewrite m-*assoc83 (suc n) d = refl
m-*assoc8 (x' ∷ xs') (x ∷ xs) d rewrite m-*assoc81 x x' (〈 xs' 〉) xs d = cong (_+_ ( x ∧ foldr (λ _ → Bool) _∨_ false (zipWith _∧_ d x'))) ((m-*assoc8 xs' xs d))


m-*assoc71 : ∀{m k l}(xs : Vec R ( m))(ds : Vec (Vec R ( k)) l)(xs' : Vec (Vec R ( k)) ( m))
  → map
      (λ x' → foldr _ _+_ zero (zipWith _*_ xs x'))
      (_⋆_ ds (〈 xs' 〉))
      ≡
      map
      (λ x' →
         foldr _ _+_ zero
         (zipWith _*_
          (map
           (λ x1 → foldr _ _+_ zero (zipWith _*_ xs x1))
           (〈 xs' 〉))
          x'))
      ds
m-*assoc71 [] [] [] = refl
m-*assoc71 (x ∷ xs) [] ys = refl
m-*assoc71 (xs) (x' ∷ xs') ys rewrite m-TT ys
 | m-*assoc8 ys (xs) x' = cong (_∷_ _) (m-*assoc71 (xs) xs' ys)


m-*assoc7 : {l k m : ℕ}(x : Vec R m)(m2 : m × k )(m3 : k × l)
  → (map (λ x' → foldr _ _+_ zero (zipWith  _*_ x x'))
      (〈 _⋆_ m2 m3 〉)) 
  ≡ 
  (map
      (λ x' →
         foldr _ _+_ zero
         (zipWith _*_
          (map
           (λ x0 → foldr _ _+_ zero (zipWith _*_ x x0))
           (〈 m2 〉))
          x'))
      (〈 m3 〉))
m-*assoc7 {nzero} {nzero} {nzero} [] [] [] = refl
m-*assoc7 {suc n} {nzero} {nzero} [] [] [] = cong (_∷_ _) (m-*assoc7 [] [] [])
m-*assoc7 {l}{k}{m}( xs) ( xs') (xs0)
  rewrite m-*assoc0 xs' (xs0) 
  with ((〈 xs0 〉)) 
... | ds = m-*assoc71  xs ds xs'



m-*assoc : ∀{m n k l}(m1 : n × m)(m2 : m × k)(m3 : k × l)
  → _⋆_ m1 (_⋆_ m2 m3) ≡ _⋆_ (_⋆_ m1 m2) m3
m-*assoc [] m2 m3 = refl
m-*assoc {m} {suc n} {k} {l}  (x ∷ xs) m2 m3 
  rewrite m-*assoc7 {l} {k} {m} x m2 m3 = cong (_∷_ _) (m-*assoc xs m2 m3)

