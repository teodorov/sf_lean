
open import Algebra.CommSemiRings

module Data.Matrix.HelperLemmas2  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality
open import Data.Matrix

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr

replicatelemm : {k l : ℕ}(x : R)
  → replicate {_} {k} x  ++ replicate {_} {l} x ≡ replicate {_} {k ✚ l} x
replicatelemm {nzero} x = refl
replicatelemm {suc n} x = cong (_∷_ _) (replicatelemm {n} x)

m-zero*4 : {n : ℕ}(v : Vec R n) 
  → zipWith _*_ (replicate zero) v ≡ replicate zero
m-zero*4 [] = refl
m-zero*4 (x ∷ xs) = ? --rewrite law10 {x} = ? --cong (_∷_ zero) (m-zero*4 xs)

m-zero*41 : {n : ℕ}(v : Vec R n) 
  → zipWith _*_  v (replicate zero) ≡ replicate zero
m-zero*41 [] = refl
m-zero*41 (x ∷ xs) rewrite law11 {x} = cong (_∷_ zero) (m-zero*41 xs)

m-zero*3 : {n : ℕ}{x : R} 
  → (foldr (\ _ → R) _+_ x (replicate {_} {n} zero)) ≡ x
m-zero*3 {nzero} = refl
m-zero*3 {suc n} {x} 
  rewrite law2 {foldr (λ _ → R) _+_ x (replicate {_} {n}  zero)}
    = m-zero*3 {n}




lemm31 : {k l m n : ℕ}(m1 : k × l)(m2 : m × l)(m3 : _ × n )
  → (m1 ++ m2) ⋆ m3 ≡ (m1 ⋆ m3) ++ (m2 ⋆ m3)
lemm31 [] m2 m3 = refl
lemm31 (x ∷ xs) m2 m3 = cong (_∷_ _) (lemm31 xs m2 m3)


lemm321 : {l n : ℕ}(x y : Vec R l)(q z : Vec R n)
  → zipWith _+_ (x ++ z) (y ++ q) ≡ (zipWith _+_ x y ++ zipWith _+_ z q)
lemm321 [] [] q z = refl
lemm321 (x ∷ xs) (y ∷ ys) q z = cong (_∷_ _) (lemm321 xs ys q z)


lemm32 : {k l n : ℕ}(m1 m3 : k × l) (m2 m4 : k × n)
  → (m1 ++++ m2) ⊹ (m3 ++++ m4) ≡ ((m1 ⊹ m3)  ++++ (m2 ⊹ m4))
lemm32 [] [] [] [] = refl
lemm32 (x ∷ xs) (y ∷ ys) (z ∷ zs) (q ∷ qs) 
  rewrite lemm32 xs ys zs qs
  | lemm321 x y q z = refl

lemm33 : {k l m : ℕ}(m1 m3 : k × l)(m2 m4 : m × l)
  → (m1 ++ m2) ⊹ (m3 ++ m4) ≡ (m1 ⊹ m3) ++ (m2 ⊹ m4)
lemm33 [] [] m2 m4 = refl
lemm33 (x ∷ xs) (y ∷ ys) m2 m4 = cong (_∷_ _) (lemm33 xs ys m2 m4)

{- postulated before -}

concatsup1111 :  {k l n : ℕ}(x : Vec R k)(y : Vec R n)(ys : n × l)(xs : k × l)
  → zipWith _∷_ (x ++ y) (xs ++ ys) 
    ≡ (zipWith _∷_ x xs) ++ (zipWith _∷_ y ys)
concatsup1111 [] y ys [] = refl
concatsup1111 (z ∷ zs) y ys (x' ∷ xs) 
  = cong (_∷_ _) (concatsup1111 zs y ys xs)

concatsup111 : {k l n : ℕ}(xs : l × k)(ys : l × n)
  →  〈 xs ++++ ys 〉 ≡ 〈 xs 〉 ++ 〈 ys 〉
concatsup111 {nzero} [] [] = refl
concatsup111 {suc n} [] [] 
  = cong (_∷_ _) (concatsup111 {n} [] [])
concatsup111 (x ∷ xs) (y ∷ ys) 
  rewrite concatsup111 xs ys = concatsup1111 x y 〈 ys 〉  〈 xs 〉

concatsup112 : {n k o : ℕ}(xs : n × k)(ys : o × k)(x : Vec R k)
  → multRow x (xs ++ ys) ≡ multRow x xs ++ multRow x ys
concatsup112 [] ys x = refl
concatsup112 (x ∷ xs) ys x' = cong (_∷_ _) (concatsup112 xs ys x')

concatsup11 : {k l n o : ℕ}(os : l × k)(xs : k × n)(ys : k × o)
  → os ⋆ (xs ++++ ys) ≡ (os ⋆ xs) ++++ (os ⋆ ys)
concatsup11 [] xs ys = refl
concatsup11 {k} {suc l} (x ∷ xs) xs' ys rewrite concatsup111 xs' ys  
 |  concatsup112 (〈 xs' 〉) (〈 ys 〉) x = cong (_∷_ _) (concatsup11 {k} {l} xs xs' ys)
{- / postulated before -}

{- postulated before -}
concat2132 : {l k n : ℕ}(x : Vec R k)(xs : k × n)(ys : k × l)
  → zipWith _∷_ x (zipWith _++_ xs ys) ≡
      zipWith _++_ (zipWith _∷_ x xs) ys
concat2132 [] [] [] = refl
concat2132 (x ∷ xs) (y ∷ ys) (z ∷ zs) 
  = cong (_∷_ _) (concat2132 xs ys zs)

concat2131 : {l k : ℕ}(ys : k × l)
  → zipWith _++_ (replicate []) ys ≡ ys
concat2131 [] = refl
concat2131 (x ∷ xs) = cong (_∷_ _) (concat2131 xs)

concatsup213 : {l k n : ℕ}(xs : l × k)(ys : n × k)
  → 〈 xs ++ ys 〉 ≡ 〈 xs 〉 ++++ 〈 ys 〉
concatsup213 [] ys rewrite concat2131 〈 ys 〉 = refl
concatsup213 (x ∷ xs) ys rewrite concatsup213 xs ys = concat2132 x  〈 xs 〉  〈 ys 〉

concatsup215 : {l k : ℕ}(x : Vec R l)(x' : Vec R k)(x0 : Vec R l)(x1 : Vec R k)
  → foldr (λ _ → R) _+_ zero
      (zipWith _*_ (x ++ x') (x0 ++ x1))
   ≡ 
  foldr (λ _ → R) _+_ zero (zipWith _*_ x x0) +
      foldr (λ _ → R) _+_ zero (zipWith _*_ x' x1)
concatsup215 [] x' [] x1 
  rewrite law2 {foldr (λ _ → R) _+_ zero (zipWith _*_ x' x1)} = refl
concatsup215 (x ∷ xs) x' (x0 ∷ xs') x1 
  rewrite law1 
    {(x * x0)}
    {foldr (λ _ → R) _+_ zero (zipWith _*_ xs xs')}
    {foldr (λ _ → R) _+_ zero (zipWith _*_ x' x1)} = cong (_+_ _) (concatsup215 xs x' xs' x1)

concatsup214 : {k l m : ℕ}(x : Vec R l)(x' : Vec R k)(ds : m × l)(fs : m × k)
  → multRow (x ++ x') (zipWith _++_ ds fs) ≡ 
     zipWith _+_ (multRow x ds) (multRow x' fs)
concatsup214 x x' [] [] = refl
concatsup214 x x' (x0 ∷ xs) (x1 ∷ xs') 
  rewrite concatsup215 x x' x0 x1 = cong (_∷_ _) (concatsup214 x x' xs xs')


concatsup212' : {l k m n : ℕ}(as : n × l)(os : n × k)(xs : l × m)(ys : k × m)
  → (as ++++ os) ⋆ (xs ++ ys) ≡ ((as ⋆ xs) ⊹  (os ⋆ ys))
concatsup212' (x ∷ zs) (x' ∷ qs) xs' ys rewrite concatsup213 xs' ys
  with (〈 xs' 〉) | (〈 ys 〉) 
... | [] | [] = cong (_∷_ _) (concatsup212' zs qs xs' ys)
... | ds | fs 
  rewrite concatsup214 x x' ds fs = cong (_∷_ _) (concatsup212' zs qs xs' ys)
concatsup212' [] [] xs' ys = refl
{- /postulated before -}


lemm181 : {k l m n : ℕ}(A : k × l)(B : k × m)(C : n × l)(D : n × m)
  → (A ++++ B) ++ (C ++++ D) ≡ (A ++ C) ++++ (B ++ D)
lemm181 [] [] C D = refl
lemm181 (x ∷ xs) (x' ∷ xs') C D = cong (_∷_ _) (lemm181 xs xs' C D)

-- addPreCol : {n m : ℕ} → m × n → m ×  (suc n)
-- addPreCol xs = zipWith _∷_ (replicate zero) xs

-- identity : {n : ℕ} → n × n
-- identity {nzero} = []
-- identity {suc n} = (one ∷ replicate zero) ∷ addPreCol identity

-- idlemma1 : {k l : ℕ}(m : k × l)
--   → zipWith _++_ (replicate (zero ∷ [])) m
--     ≡ zipWith _∷_ (replicate zero) m
-- idlemma1 [] = refl
-- idlemma1 (x ∷ xs) = cong (_∷_ _) (idlemma1 xs)

-- idlemma : (n : ℕ)
--   → id {n} ≡ identity {n}
-- idlemma nzero = refl
-- idlemma (suc n) rewrite idlemma n | idlemma1 (identity {n})  = refl 


-- htmain2211 : {k l : ℕ}(a c : Vec R k)(b d : Vec R l)
--  → (a ++ b) ≡ (c ++ d)
--  → (a ≡ c)
-- htmain2211 [] [] b d p = refl
-- htmain2211 (true ∷ xs) (true ∷ ys) xs' ys' p = cong (_∷_ _) (htmain2211 xs ys xs' ys' (cong (λ q → tail q) p))
-- htmain2211 (true ∷ xs) (false ∷ ys) xs' ys' ()
-- htmain2211 (false ∷ xs) (true ∷ ys) xs' ys' ()
-- htmain2211 (false ∷ xs) (false ∷ ys) xs' ys' p = cong (_∷_ _) (htmain2211 xs ys xs' ys' (cong (λ q → tail q) p))


-- -- make it more general
-- takeinit0 : {k n : ℕ}(ys : Vec R n)(zs : Vec R k)
--  →  (take n (ys ++ zs)) ≡ ys
-- takeinit0 {_} {n} ys zs 
--  with splitAt n (ys ++ zs)
-- ... | (d1 , d2 , prf) rewrite prf = sym (htmain2211 ys d1 zs d2 prf)



-- takeinit : {l k : ℕ}(os : Matrix (l ✚ k) 1) → os ≡ (take' {k} l os) ++++ (init' {l} {k} os)
-- takeinit {nzero} (x ∷ []) = refl
-- takeinit {suc n} {k} (xs ∷ []) with splitAt (suc n) xs
-- takeinit {suc n} {k} (.(y ∷ ys ++ zs) ∷ []) | (y ∷ ys , zs , refl) 
--  rewrite takeinit0 ys zs = refl

-- take' : {k : ℕ}(l : ℕ)(os : 1 × (l ✚ k)) → 1 × l
-- take' l (x ∷ []) = (take l x) ∷ [] 

-- init' : {l k : ℕ}(os : 1 × (l ✚ k) ) → 1 × k
-- init' {l} (x ∷ []) = (drop l x) ∷ []
