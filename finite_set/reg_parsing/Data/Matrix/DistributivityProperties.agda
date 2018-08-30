
open import Algebra.CommSemiRings

module Data.Matrix.DistributivityProperties  where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality
open import Algebra.Logic

open import Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties
open CommSemiRing bsr

open import Data.Matrix.MultZeroProperties 
open import Data.Matrix.TransposeProperties



{- PROPERTY: distributive property: (m' + m'') * m = m' * m  + m'' * m -}

m-+*distrib4 : {x x' x0 : R} →  ((x + x') * x0) + zero ≡ ((x * x0) + zero) + ((x' * x0) + zero)
m-+*distrib4 {x} {x'} {x0} rewrite law9 {x} {x'} {x0} | law3 {x * x0} | law3 {x' * x0} | law3 {((x * x0) + (x' * x0))} = refl

m-+*distrib3 : {n : ℕ } → zipWith {n} _+_ (replicate zero) (replicate zero) ≡ replicate zero
m-+*distrib3 {nzero} = refl
m-+*distrib3 {suc n}  = cong (_∷_ _) m-+*distrib3 


m-+*distrib5 : {a b c d : R} → (a + b) + (c + d) ≡ (a + c) + (b + d)
m-+*distrib5 {a} {b} {c} {d} rewrite law1 {a} {b} {c + d} | law4 {c} {d} | sym (law1 {b} {d} {c}) | law4 {b + d} {c} | sym (law1 {a} {c} {b + d}) = refl

m-+*distrib21 : {m : ℕ}(xs ys qs : Vec R m)
     → (foldr _ _+_ zero
      (zipWith _*_ (zipWith _+_ xs ys) qs))

     ≡ 
     ((foldr _ _+_ zero (zipWith _*_ xs qs)) +
      (foldr _ _+_ zero (zipWith _*_ ys qs)))
m-+*distrib21 [] [] []  = refl
m-+*distrib21  (x ∷ xs) (y ∷ ys) (q ∷ qs) rewrite law9 {x} {y} {q} | m-+*distrib5 {(x * q)} {foldr _ (_+_) zero (zipWith _*_ xs qs)} {y * q} {foldr _ _+_ zero (zipWith _*_ ys qs)} = cong (_+_ ((x ∧ q ∨ y ∧ q))) ((m-+*distrib21 xs ys qs))

m-+*distrib2 : {m n : ℕ}{x y q : R}(xs ys qs : Vec R m)
     → ((x + y) * q) +
      foldr _ _+_ zero
      (zipWith _*_ (zipWith _+_ xs ys) qs) 

     ≡ 

     ((x * q) +
       foldr _ _+_ zero (zipWith _*_ xs qs))
      +
      ((y * q) +
       foldr _ _+_ zero (zipWith _*_ ys qs))
m-+*distrib2 {m} {n} {x} {y} {q} xs ys qs rewrite law9 {x} {y} {q} | m-+*distrib5 {(x * q)} {foldr _ (_+_) zero (zipWith _*_ xs qs)} {y * q} {foldr _ _+_ zero (zipWith _*_ ys qs)} = cong (_+_ (x ∧ q ∨ y ∧ q)) (m-+*distrib21 {m} xs ys qs)
--




m-+*distrib0 : {m k : ℕ}(x : Vec R (suc m))(y : Vec R (suc m))(z : Vec R (suc k))(zs : Vec (Vec R (suc k)) m) 
  → multRow (zipWith _+_ x y) (zipWith _∷_ z (〈 zs 〉)) ≡ 
    zipWith _+_ (multRow x (zipWith _∷_ z (〈 zs 〉)))
      (multRow y (zipWith _∷_ z (〈 zs 〉)))

m-+*distrib0 {nzero} {nzero} (x ∷ []) (x' ∷ []) (x0 ∷ []) [] rewrite m-+*distrib4 {x} {x'} {x0} = cong (_∷_ _) refl
m-+*distrib0 {nzero} {suc n} (x ∷ []) (x' ∷ []) (x0 ∷ xs0) [] rewrite m-+*distrib4 {x} {x'} {x0} =  cong (_∷_ _) (m-+*distrib0 (x ∷ []) (x' ∷ []) xs0 [])


m-+*distrib0 {suc m} {nzero} (x ∷ xs) (x' ∷ xs') (x0 ∷ []) (x1 ∷ xs1) with (zipWith _∷_ x1 (〈 xs1 〉))
... | q ∷ [] rewrite m-+*distrib2 {suc m} {nzero} {x} {x'} {x0} xs xs' q  = cong (_∷_ _) refl

m-+*distrib0 {suc m} {suc n} (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (x1 ∷ xs1) with (zipWith _∷_ x1 (〈 xs1 〉))
... | q ∷ qs  rewrite m-+*distrib2 {suc m} {suc n} {x} {x'} {x0} xs xs' q = cong (_∷_ _) (subst2 (\ hs →  multRow (zipWith _+_ (x ∷ xs) (x' ∷ xs')) ( zipWith _∷_ xs0 hs) ≡ zipWith _+_ (multRow (x ∷ xs) (zipWith _∷_ xs0 hs)) (multRow (x' ∷ xs') (zipWith _∷_ xs0 hs))) ((m-+*distrib0 (x ∷ xs) (x' ∷ xs') xs0 (〈 qs 〉))) (m-TT qs)) 


m-+*distrib : {m n k : ℕ}(m1 : n × m)(m2 : n × m)(m3 : m × k) → multiply (m1 ⊹ m2) m3 ≡ ((multiply m1 m3) ⊹ (multiply m2 m3)) 
m-+*distrib [] [] m3 = refl
m-+*distrib {nzero} {suc n} {k} ([] ∷ xs) ([] ∷ xs') [] rewrite m-zero*1 {k} | m-+*distrib3 {k} = cong (_∷_ _) (m-+*distrib xs xs' [])
m-+*distrib {suc m} {suc n} {nzero} (x ∷ xs) (x' ∷ xs') ([] ∷ xs0) with (〈 xs0 〉)
... | [] = cong (_∷_ _) (m-+*distrib xs xs' ([] ∷ xs0))
m-+*distrib {suc m} {suc n} {suc k} (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite m-+*distrib0 {m} {k} x y z zs = cong (_∷_ _) (m-+*distrib xs ys (z ∷ zs))



{- PROPERTY: distributive property:  m*(m' + m'') = m * m'  + m * m'' -}



m-*distrib3 : {n n' : ℕ}(is js : Vec R n)(ds fs : Vec (Vec R n') n) →  zipWith _∷_ (zipWith _+_ is js) (ds ⊹ fs) ≡
       (zipWith _∷_ is ds) ⊹ (zipWith _∷_ js fs)
m-*distrib3 [] [] [] [] = refl
m-*distrib3 (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (x1 ∷ xs1) = cong (_∷_ _) (m-*distrib3 xs xs' xs0 xs1)

m-*distrib2 : {m n : ℕ}(xs ys : n × m)
 → (〈_〉 (xs ⊹ ys)) ≡ (〈 xs 〉) ⊹ (〈 ys 〉)
m-*distrib2 {nzero} {nzero} [] [] = refl
m-*distrib2 {suc n} {nzero} [] [] = cong (_∷_ _) (m-*distrib2 [] [])
m-*distrib2 {nzero} {suc n} ([] ∷ xs) ([] ∷ xs')
  with  (zipWith _∷_ [] (〈 xs' 〉)) |  zipWith _∷_ [] (〈_〉 (xs ⊹ xs')) | (zipWith _∷_ [] (〈 xs 〉))
... | [] | [] | [] = refl
m-*distrib2 {suc n} {suc n'} ((i ∷ is) ∷ xs) ((j ∷ js) ∷ xs') rewrite m-*distrib2 {suc n} {n'} xs xs' 
  with (〈 xs 〉) | (〈 xs' 〉)
... | d ∷ ds | f ∷ fs = cong (_∷_ _) (m-*distrib3 is js ds fs)


f : {n : ℕ}(z : Vec R n) → (x : Vec R n) → R
f z = (λ x' → foldr (_) (_+_) zero (zipWith _*_ z x'))


m-*distrib8 : (a b c d : R) → (a + b) + (c + d) ≡ (a + c) + (b + d)
m-*distrib8 a b c d 
  rewrite law1 {a} {b} {c + d} | (sym (law1 {b} {c} {d})) |
    law4 {b} {c} | law1 {c} {b} {d} | (sym (law1 {a} {c} {b + d})) = refl

m-*distrib4 : {m : ℕ}{i j : R}(d z : Vec R m)(g : Vec R (suc m))
  → f g (i + j ∷ zipWith _+_ d z)  
  ≡ 
  (f g (i ∷ d) + f g (j ∷ z))
m-*distrib4 {nzero} {i} {j} [] [] (x ∷ []) 
  rewrite law3 {(x * (i + j))} | law3 {x * i} | law3 {x * j} | law8 {x} {i} {j} = refl
m-*distrib4 {suc m} {i} {j} (x ∷ xs) (z ∷ zs) (g ∷ gs) rewrite law8 {g} {i} {j} | m-*distrib8 (g * i) (foldr _ _+_ zero (zipWith _*_ gs (x ∷ xs))) (g * j) (foldr _ _+_ zero (zipWith _*_ gs (z ∷ zs)))  = cong (_+_ ((g ∧ i ∨ g ∧ j))) (m-*distrib4 xs zs gs)
--


m-*distrib6 : {m : ℕ}{x2 x' x : R}(xs2 x1 x0 : Vec R m)
  → ((x2 * (x' + x)) +
      foldr _ _+_ zero
      (zipWith _*_ xs2 (zipWith _+_ x1 x0))) ≡ 
      (((x2 * x') +
       foldr _ _+_ zero (zipWith _*_ xs2 x1))
      +
      ((x2 * x) +
       foldr _ _+_ zero (zipWith _*_ xs2 x0)))
m-*distrib6 {m} {x2} {x'} {x} xs2 x1 x0 = m-*distrib4 x1 x0 (x2 ∷ xs2)


m-*distrib5 : {n m : ℕ}(js : Vec R n)(is : Vec R n)(fs : Vec (Vec R m) n)(ds : Vec (Vec R m) n)(g : Vec R (suc m))
  → map (f g) (zipWith _∷_ (zipWith _+_ is js) (ds  ⊹ fs)) ≡ (zipWith _+_ (map (f g) (zipWith _∷_ is ds)) (map (f g) (zipWith _∷_ js fs)))
m-*distrib5 [] [] [] [] g = refl
m-*distrib5 {suc n} {m} (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (x1 ∷ xs1) (x2 ∷ xs2) rewrite m-*distrib6 {m} {x2} {x'} {x} xs2 x1 x0 = cong (_∷_ _) (m-*distrib5 xs xs' xs0 xs1 (x2 ∷ xs2))


m-*distrib1 : {m n : ℕ}(xs ys : m × n)(g : Vec R m)
  → map (f g) (〈_〉 (xs ⊹ ys)) ≡ zipWith _+_ (map (f g) (〈 xs 〉)) (map (f g) (〈 ys 〉))
m-*distrib1 {nzero} {nzero} [] [] [] = refl
m-*distrib1 {nzero} {suc n} [] [] [] = cong (_∷_ _) (m-*distrib1 [] [] [])
m-*distrib1 {suc m} {nzero} ([] ∷ xs) ([] ∷ xs') g 
  with  (zipWith _∷_ [] (〈_〉 (xs ⊹ xs'))) |  (zipWith _∷_ [] (〈 xs 〉)) |  (zipWith _∷_ [] (〈 xs' 〉))
... | [] | [] | [] = refl
m-*distrib1 {suc m} {suc n} ((i ∷ is) ∷ xs) ((j ∷ js) ∷ xs') g rewrite m-*distrib2 {suc n} {m} xs xs' 
  with (〈 xs 〉) | (〈 xs' 〉)
... | d ∷ ds | z ∷ fs rewrite m-*distrib4 {_} {i} {j} d z g = cong (_∷_ _) (m-*distrib5 js is fs ds g)


m-*+distrib0 : {m n k : ℕ}(m2 : Vec (Vec R m) n)(m3 : Vec (Vec R m) n)(xs : Vec (Vec R n) k)(x : Vec R n) 
  → (map
      (λ x' → foldr _ _+_ zero (zipWith _*_ x x'))
      (〈_〉 (m2 ⊹ m3))) ≡ 
    (zipWith _+_
      (map
       (λ x' → foldr _ _+_ zero (zipWith _*_ x x'))
       (〈 m2 〉))
      (map
       (λ x' → foldr _ _+_ zero (zipWith _*_ x x'))
       (〈 m3 〉)))
m-*+distrib0 m2 m3 xss z = m-*distrib1 m2 m3 z

m-*+distrib : {m n k : ℕ}(m1 : k × n)(m2 : n × m)(m3 : n × m)
  → m1 ⋆ (m2 ⊹ m3) ≡ ((m1 ⋆ m2) ⊹ (m1 ⋆ m3)) 
m-*+distrib [] m2 m3 = refl
m-*+distrib {m} {nzero} {suc k} (x ∷ xs) m2 m3 
  rewrite m-*+distrib0 {m} {nzero} {k} m2 m3 xs x = cong (_∷_ _) (m-*+distrib xs m2 m3)
m-*+distrib  {m}{n}{suc k} (x ∷ xs) m2 m3
  rewrite m-*+distrib0 m2 m3 xs x = cong (_∷_ _) (m-*+distrib xs m2 m3)
