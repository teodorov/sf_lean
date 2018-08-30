
open import Algebra.CommSemiRings

module Data.Matrix.JoinProperties where
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality



import Data.Matrix; open Data.Matrix
import Data.Matrix.TransposeProperties; open Data.Matrix.TransposeProperties

open import Data.Bool
open import Data.Bool.CommRingProperties
open CommSemiRing bsr

{-
joinlemma0 : ∀{n m l k}(is : Vec R n)(fs : Vec (Vec R m) n)(ds : Vec (Vec R l) (suc k))(x' : Vec R (suc k))
  →  zipWith _∷_ (is ++ zero ∷ replicate zero)
      (join fs (zipWith _∷_ x'  ds))
      ≡ join (zipWith _∷_ is fs) (zipWith _∷_ x' ds)
joinlemma0 [] [] ds x' = refl
joinlemma0 (x ∷ xs) (x' ∷ xs') ds x0 = cong (_∷_ _) (joinlemma0 xs xs' ds x0)


joinlemma01 : ∀{m n k}(is : Vec R n)(ds : n × m)
 →   zipWith _∷_ (is ++ []) (join {m} {k}  ds []) ≡
            join (zipWith _∷_ is ds) []
joinlemma01 [] [] = refl
joinlemma01 (x ∷ xs) (x' ∷ xs') = cong (_∷_ _) (joinlemma01 xs xs')

joinlemma02 : ∀{n m k}(is : Vec R n)(ds : Vec (Vec R m) n)
  → zipWith _∷_ (is ++ zero ∷ replicate {_} {k} zero)
      (join ds ([] ∷ replicate []))
      ≡ join (zipWith _∷_ is ds) ([] ∷ replicate [])
joinlemma02 [] [] = refl
joinlemma02 (x ∷ xs) (x' ∷ xs') = cong (_∷_ _) (joinlemma02 xs xs')

joinlemma05 : {n m : ℕ}(xs0 : Vec R n)(xs : n × m)
  → (〈_〉 (zipWith _∷_ xs0 xs)) ≡ xs0 ∷ (〈 xs 〉)
joinlemma05 [] [] = refl
joinlemma05 (x ∷ xs) (x' ∷ xs') rewrite joinlemma05 xs xs' = refl

joinlemma06 : (n : ℕ)
  → 〈_〉 (addPreCols ([] ∷ []) n) ≡ join {nzero} {suc nzero} {n} (replicate []) []
joinlemma06 nzero = refl
joinlemma06 (suc n)  rewrite joinlemma05 (zero ∷ []) (addPreCols ([] ∷ []) n) = cong (_∷_ _) (joinlemma06 n)

joinlemma07 : {k : ℕ}(xs : Vec R (suc k))(n' : ℕ)
  → 〈_〉 (addPreCols (xs ∷ []) n') ≡
      join {nzero} {suc 0} {n'} (replicate []) (zipWith _∷_ xs ([] ∷ replicate []))
joinlemma07 (x ∷ xs) nzero = refl
joinlemma07 (x ∷ xs) (suc n) rewrite joinlemma05 (zero ∷ []) (addPreCols ((x ∷ xs) ∷ []) n) = cong (_∷_ _) (joinlemma07 (x ∷ xs) n)

joinlemma03 : ∀{k l}(x : Vec R k)(xs : l × k)(n : ℕ)
  → 〈_〉
      (zipWith _∷_ (zero ∷ replicate zero) (addPreCols (x ∷ xs) n))
      ≡
      (zero ∷ replicate zero) ∷
      join {nzero} {suc l} {n}(replicate []) (zipWith _∷_ x (〈 xs 〉))
joinlemma03 [] [] n rewrite joinlemma05 (zero ∷ []) (addPreCols ([] ∷ []) n) = cong (_∷_ _) (joinlemma06 n )
joinlemma03 [] ([] ∷ xs) (suc n') rewrite joinlemma05 (zero ∷ zero ∷ replicate zero) (addPreCols ([] ∷ [] ∷ xs) (suc n')) = cong (_∷_ _) (joinlemma03 [] ([] ∷ xs) n')
joinlemma03 [] ([] ∷ xs) (nzero) rewrite joinlemma05 (replicate zero) xs = refl
joinlemma03 (x ∷ xs) [] nzero = refl
joinlemma03 {suc k} {nzero} (xs) [] (suc n') 
  rewrite joinlemma05 (zero ∷ []) (zipWith _∷_ (zero ∷ []) (addPreCols (xs ∷ []) n')) |
    joinlemma05 (zero ∷ []) (addPreCols (xs ∷ []) n') = cong (_∷_ _) (cong (_∷_ _) (joinlemma07 xs n'))
joinlemma03 (x ∷ xs) (x' ∷ xs') nzero rewrite joinlemma05 ((replicate zero)) (xs')  = cong (_∷_ _) refl
joinlemma03 (x ∷ xs) (x' ∷ xs') (suc n) rewrite joinlemma05 ((zero ∷ zero ∷ replicate zero)) ((addPreCols ((x ∷ xs) ∷ x' ∷ xs') (suc n))) 
  = cong (_∷_ _) (joinlemma03 (x ∷ xs) (x' ∷ xs') n)
--  rewrite joinlemma05 (zero ∷ zero ∷ replicate zero)  = {!!}
--joinlemma03 (x ∷ xs) ((i ∷ is) ∷ xs') (suc n0) = {!!}


joinlemma04 : {n m : ℕ}
  → replicate {_} {n ✚ m} [] ≡ join (replicate {_} {n} []) (replicate {_} {m} [])
joinlemma04 {nzero} = refl
joinlemma04 {suc n} = cong (_∷_ []) (joinlemma04 {n})

joinlemma : ∀{n m k l}(m1 : m × n)(m2 : l × k)
 → 〈_〉 (join m1 m2) ≡ join (〈 m1 〉) (〈 m2 〉)
joinlemma {nzero} {nzero} [] [] = refl
joinlemma {suc n} {nzero} {nzero} [] [] with (zipWith _∷_ [] (addPreCols {nzero} [] n))
... | [] = cong (_∷_ _) (joinlemma04 {n} {nzero})
joinlemma {suc n} {nzero} {suc n'} [] [] with (zipWith _∷_ [] (addPreCols {suc n'} [] n))
... | [] = cong (_∷_ _) (joinlemma04 {n} {suc n'})
joinlemma {nzero} {nzero} {k} {suc l} [] (x ∷ xs) = refl
joinlemma {suc n} {nzero} {k} {suc l} [] (x ∷ xs) = joinlemma03 x xs n

joinlemma {nzero} {suc m} {nzero} {nzero} ([] ∷ xs) [] 
  with zipWith _∷_ [] (〈_〉 (join xs [])) | zipWith _∷_ [] (〈 xs 〉) 
... | [] | [] with zipWith _∷_ [] (addPreCols {nzero} [] m)
... | [] = refl
joinlemma {nzero} {suc m} {suc n} {nzero} ([] ∷ xs) [] 
  rewrite joinlemma {nzero} {m} {suc n} {nzero} xs []  
  with (〈 xs 〉)
... | [] = refl
joinlemma {suc n} {suc m} {nzero} {nzero} ((i ∷ is) ∷ xs) [] 
  rewrite joinlemma {suc n} {m} {nzero} {nzero} xs [] 
  with (〈 xs 〉) 
... | d ∷ ds = cong (_∷_ _) (joinlemma01 is ds)
joinlemma {suc n} {suc m} {suc k} {nzero} ((i ∷ is) ∷ xs) [] 
  rewrite joinlemma {suc n} {m} {suc k} {nzero} xs [] 
  with (〈 xs 〉)
... | d ∷ ds = cong (_∷_ _) (joinlemma02 is ds)

joinlemma {n} {suc m} {k} {suc l} (x ∷ xs) (x' ∷ xs') 
  rewrite joinlemma xs (x' ∷ xs')
    with (〈 xs' 〉) | (〈 xs 〉)
joinlemma {nzero} {suc m} {suc k} {suc l} ([] ∷ xs) (x' ∷ xs')  | d ∷ ds | []  = refl
joinlemma {suc n} {suc m} {suc k} {suc l} ((i ∷ is) ∷ xs) (x' ∷ xs')  | d ∷ ds | f ∷ fs  
  = cong (_∷_ _) (joinlemma0 is fs (d ∷ ds) x')
joinlemma {nzero} {suc m} {nzero} {suc l} ([] ∷ xs) ([] ∷ xs')  | [] | []  = refl
joinlemma {suc n} {suc m} {nzero} {suc l} ((i ∷ is) ∷ xs) ([] ∷ xs')  | [] | f ∷ fs  = cong (_∷_ _) (joinlemma01 is fs)

{-
joinlemma : ∀{n m k l}(m1 : m × n)(m2 : l × k)
 → 〈_〉 (join m1 m2) ≡ join (〈 m1 〉) (〈 m2 〉)
joinlemma = {!!}
-}

jjmlemma021 : (n : ℕ)
  → (zipWith _*_ (replicate {_} {n} zero) (replicate {_} {n} zero)) 
    ≡ (replicate {_} {n} zero)
jjmlemma021 nzero = refl
jjmlemma021 (suc n) = cong (_∷_ _) (jjmlemma021 n)

jjmlemma022 : (n : ℕ)
  → foldr _ _+_ zero (replicate {_} {n} zero) ≡ zero
jjmlemma022 nzero = refl
jjmlemma022 (suc n) = jjmlemma022 n

jjmlemma02 : {m n : ℕ}(xs : Vec R n)(d : Vec R n)
  → foldr _ _+_ zero
      (zipWith _*_ (xs ++ replicate {_} {m} zero) (d ++ replicate zero)) ≡ 
  foldr _ _+_ zero (zipWith _*_  xs d)
jjmlemma02 {m} {nzero} [] [] rewrite jjmlemma021 m | jjmlemma022 m = refl
jjmlemma02 (x ∷ xs) (d ∷ ds) = cong (_+_  (x * d)) ((jjmlemma02 xs ds)) 


jjmlemma05 : {n m : ℕ}(x : R)(xs : Vec R  n)(m : m × n)
  → multRow (x ∷ xs) (zipWith _∷_ (replicate zero) m) ≡ multRow xs m
jjmlemma05 x [] [] = refl
jjmlemma05 x [] ([] ∷ xs) rewrite law11 {x}  = cong (_∷_ _) (jjmlemma05 x [] xs)
jjmlemma05 x (x' ∷ xs) [] = refl
jjmlemma05 x (x' ∷ xs) (x0 ∷ xs') rewrite law11 {x}  = cong (_∷_ _) (jjmlemma05 x (x' ∷ xs) xs')


jjmlemma0121 : {n : ℕ}(x : Vec R n)
  → (zipWith _*_ (replicate zero) x) ≡ replicate zero
jjmlemma0121 [] = refl
jjmlemma0121 (x ∷ xs)  = cong (_∷_ _) (jjmlemma0121 xs)

jjmlemma0122 : (n : ℕ)
  → foldr _ _+_ zero (replicate {_} {n} zero) 
  ≡ zero
jjmlemma0122 nzero = refl
jjmlemma0122 (suc n) = jjmlemma0122 n

jjmlemma04 : {k2 n2 n3 : ℕ}(xs : Vec R k2)(ds : n3 × n2)
  → multRow (xs ++ replicate {_} {n2} zero)
      (addPreCols ds k2)
      ≡ replicate zero
jjmlemma04 [] [] = refl
jjmlemma04 {nzero} {n2} [] (x ∷ xs) rewrite jjmlemma0121 x |
  jjmlemma0122 n2 = cong (_∷_ _) (jjmlemma04 [] xs)
jjmlemma04 {suc k2} {n2} (x ∷ xs) [] with  (zipWith _∷_ [] (addPreCols {n2} [] k2))
... | [] = refl
jjmlemma04 {suc k2} {n} {suc n3} (x ∷ xs) xs' 
  rewrite jjmlemma05 x ((xs ++ replicate zero)) ( (addPreCols xs' k2)) = jjmlemma04 xs xs'


jjmlemma03 : {k2 k3 n2 n3 : ℕ}(xs : Vec R k2)(ds : k3 × k2)(m4 : n2 × n3)
  → multRow (xs ++ replicate zero) (join ds (〈 m4 〉)) ≡
      multRow xs ds ++ replicate zero
jjmlemma03 {k2} {nzero} {n2} {n3} xs [] ds = jjmlemma04 {k2} {n2} {n3} xs (〈 ds 〉)
jjmlemma03 {k2} {suc k3} {n2} (xs) (x' ∷ xs') m4
  rewrite jjmlemma02 {n2} (xs) (x')  = cong (_∷_ _) (jjmlemma03 (xs) xs' m4)


jjmlemma011 : (n : ℕ)
  → multRow [] (replicate {_} {n} []) ≡ replicate zero
jjmlemma011 nzero = refl
jjmlemma011 (suc n) = cong (_∷_ _) (jjmlemma011 n)



jjmlemma012 : {m n : ℕ}(xss : n × m)
  → multRow (replicate zero) xss ≡ replicate zero
jjmlemma012 [] = refl
jjmlemma012 {m} (x ∷ xs) 
  rewrite jjmlemma0121 x | jjmlemma0122 m = cong (_∷_ _) (jjmlemma012 xs)

jjmlemma013 : (n m : ℕ)
  → replicate {_} {n} zero ++ replicate {_} {m} zero ≡ 
    replicate {_} {n ✚ m} zero
jjmlemma013 nzero m = refl
jjmlemma013 (suc n) m = cong (_∷_ _) (jjmlemma013 n m)


jjmlemma01 : ∀{k2 k3 n2 n3}(x : Vec R k2)(m3 : Vec (Vec R k3) k2)(m4 : Vec (Vec R n3) n2)
  → multRow (x ++ replicate zero) (〈_〉 (join m3 m4)) 
    ≡ 
    (multRow x (〈 m3 〉) ++ replicate zero)
jjmlemma01 {nzero} {nzero} [] [] m4 
  rewrite jjmlemma012 (〈 m4 〉) = refl
jjmlemma01 {nzero} {suc n} {n2} {n3} [] [] m4 
  rewrite jjmlemma011 n  | jjmlemma012
  (〈_〉 (zipWith _∷_ (replicate zero) (addPreCols m4 n))) |
  jjmlemma013 n n3 = refl
jjmlemma01 {suc k2} {_} {n2} (x ∷ xs) m3 m4 rewrite joinlemma m3 m4 
  with (〈 m3 〉) 
jjmlemma01 {suc k2} {nzero} {n2} (x ∷ xs) m3 m4 | ds 
  rewrite jjmlemma03 (x ∷ xs) ds m4 =  refl
jjmlemma01 {suc k2} {suc k3} {n2} (x ∷ xs) m3 m4 | d ∷ ds 
  rewrite jjmlemma02 {n2} (x ∷ xs) d = cong (_∷_ _) (jjmlemma03 (x ∷ xs) ds m4)



jmlemma07111 : {n : ℕ}(xs : Vec R n)
  → foldr _ _+_ zero
      (zipWith _*_ xs (replicate zero)) ≡ zero
jmlemma07111 [] = refl
jmlemma07111 (x ∷ xs) rewrite law11 {x} = jmlemma07111 xs



jmlemma0711 : ∀{k n}(x : Vec R n)(m2 : n × k)
  → (zero ∷
       map
       (λ x' → foldr _ _+_ zero (zipWith _*_ x x'))
       (〈 m2 〉)) ≡ 
       map
      (λ x' → foldr _ _+_ zero (zipWith _*_ x x'))
      (〈_〉 (zipWith _∷_ (replicate zero) m2))
jmlemma0711 [] [] = refl
jmlemma0711 (x ∷ xs) (x' ∷ xs')
  rewrite m-TT1 xs' (replicate zero) | law11 {x} | jmlemma07111 xs   = cong (_∷_ _) refl
   


jmlemma071 : ∀{n m k}(m1 : m × n)(m2 : n × k)
  → zipWith _∷_ (replicate zero) (multiply' m1 m2) ≡ multiply' m1 (zipWith _∷_ (replicate zero) m2)
jmlemma071 [] m2 = refl
jmlemma071 (x ∷ xs) m2 rewrite jmlemma0711 x m2  = cong (_∷_ _) (jmlemma071 xs m2)



jmlemma07 : {k3 n2 n n3 : ℕ}(m2 : n × n2)(m4 : n2 × n3)
  → addPreCols (multiply' m2 m4) k3 ≡ multiply' m2 (addPreCols m4 k3)
jmlemma07 {nzero} m1 m2 = refl
jmlemma07 {suc n} m1 m2 rewrite jmlemma07 {n} m1 m2 
  with (addPreCols m2 n) 
... | ds =  jmlemma071 m1 ds


jmlemma061 : ∀{m k}(x : Vec R m)(ys : Vec R k)(yss : k × m)
  → map
      (λ x' →
         foldr _ _+_ zero (zipWith _*_ (zero ∷ x) x'))
      (zipWith _∷_ ys yss) ≡ 
  map
      (λ x' → foldr _ _+_ zero (zipWith _*_ x x')) yss
jmlemma061 [] [] [] = refl
jmlemma061 [] (x ∷ xs) ([] ∷ xs') = cong (_∷_ _) (jmlemma061 [] xs xs')
jmlemma061 (x ∷ xs) [] [] = refl
jmlemma061 (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) = cong (_∷_ _) (jmlemma061 (x ∷ xs) xs' xs0)

jmlemma06 : {m n k : ℕ}(xss : n × m)(yss : m × k)(ys : Vec R k)
  → multiply' (zipWith _∷_ (replicate zero) xss) (ys ∷ yss) ≡ multiply' xss yss
jmlemma06 [] yss ys = refl
jmlemma06 (x ∷ xs) yss ys rewrite jmlemma061 x ys (〈 yss 〉) = cong (_∷_ _) (jmlemma06 xs yss ys)


jmlemma08 : ∀{n n2 n3 k2 k3}(m2 : n × n2)(m4 : n2 × n3)(xs : k2 × k3)
  → multiply' (addPreCols m2 k2) (join xs m4) ≡
      multiply' m2 (addPreCols m4 k3)
jmlemma08 {nzero} {n2} {n3} {k2} [] m2 xs with (addPreCols {n2} [] k2)
... | []  = refl
jmlemma08 (x ∷ xs) m2 [] = refl
jmlemma08 {suc n} {n2} {n3} {suc k2} {k3} (xs) m2 (x' ∷ xs')
  rewrite jmlemma06 (addPreCols (xs) k2) (join xs' m2) (x' ++ replicate zero) = jmlemma08 xs m2 xs'




jmlemma : {k n k2 n2 k3 n3 : ℕ} 
               → (m1 : k × k2) → (m2 : n × n2) 
               → (m3 : k2 × k3) → (m4 : n2 × n3) 
               → multiply' ((join m1 m2)) (join m3 m4) ≡ 
                          join (multiply' m1 m3) (multiply' m2 m4)
jmlemma {nzero} {n} {nzero} {n2} {k3} {n3} [] m2 [] m4 rewrite jmlemma07 {k3} {n2} {n} {n3} m2 m4 = refl

jmlemma {nzero} {n} {suc k2} {n2} {k3} {n3} [] m2 (x ∷ xs) m4 
 rewrite jmlemma06 (addPreCols m2 k2) (join xs m4) ((x ++ replicate zero)) |
 jmlemma07 {k3} {n2} {n} {n3} m2 m4 = jmlemma08 m2 m4 xs

jmlemma {suc n} xs m2 m3 m4 rewrite  sym (ml  (join xs m2) (join m3 m4)) 
  | sym (ml xs m3) | sym (ml m2 m4) = jmlemma- xs m2 m3 m4
  where
    jmlemma- : {k n k2 n2 k3 n3 : ℕ} 
               → (m1 : (suc k) × k2) → (m2 : n × n2) 
               → (m3 : k2 × k3) → (m4 : n2 × n3) 
               → multiply ((join m1 m2)) (join m3 m4) ≡ 
                          join (multiply m1 m3) (multiply m2 m4)
    jmlemma-  (x ∷ xs) m2 m3 m4 rewrite jjmlemma01 x m3 m4 |
      ml xs m3 | ml m2 m4 | ml (join xs m2) (join m3 m4) = cong (_∷_ _) (jmlemma xs m2 m3 m4)


-}
