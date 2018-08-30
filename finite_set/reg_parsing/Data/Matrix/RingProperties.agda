
open import Algebra.CommSemiRings

module Data.Matrix.RingProperties where

open import Relation.Binary.PropositionalEquality
import Data.Matrix
open Data.Matrix
open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl ; null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)

open import Data.Bool
open import Data.Bool.CommRingProperties

open CommSemiRing bsr

import Data.Matrix.AdditionProperties
open Data.Matrix.AdditionProperties 

import Data.Matrix.MultAssocProperties
open Data.Matrix.MultAssocProperties 

import Data.Matrix.MultIdentProperties
open Data.Matrix.MultIdentProperties 

import  Data.Matrix.DistributivityProperties
open  Data.Matrix.DistributivityProperties 

import  Data.Matrix.MultZeroProperties
open  Data.Matrix.MultZeroProperties 



--import  Data.Matrix.JoinProperties
--open  Data.Matrix.JoinProperties renaming (joinlemma to joinlemma')

mrl : {n m : ℕ}(v : Vec R n)(xs : m × n)
  → multRow v xs ≡ multRow' v xs
mrl xs [] = refl
mrl xs (x' ∷ xs') = cong (_∷_ _) (mrl xs xs')

ml : {n m k : ℕ}(m1 : m × n)(m2 : n × k)
  → multiply m1 m2 ≡ m1 ⋆ m2 
ml [] m2 = refl
ml (x ∷ xs) xs' 
  rewrite mrl x 〈 xs' 〉 = cong (_∷_ _) (ml xs xs')

mlaw3 : {n m : ℕ} → (m1 m2 m3 : m × n) 
  → m1 ⊹ (m2 ⊹ m3) ≡ (m1 ⊹ m2) ⊹ m3
mlaw3 m1 m2 m3 = m-+assoc m1 m2 m3

mlaw21 :  {n m : ℕ}(xss : m × n) 
  → (null {m} {n}) ⊹ xss ≡ xss
mlaw21 xss = m-+zero xss

mlaw6 : {n m : ℕ}(xss : m × n)
  → xss ⊹ (null {m} {n}) ≡ xss
mlaw6 xss = m-zero+ xss 

mlaw4 : {n m : ℕ}(m1 : m × n)(m2 : m × n) 
  → m1 ⊹ m2 ≡ m2 ⊹ m1
mlaw4 m1 m2 = m-+comm m1 m2

mlaw5 : ∀{m n k l}(m1 : n × m)(m2 : m × k)(m3 : k × l)
  → (m1 ⋆ m2) ⋆ m3 ≡ m1 ⋆ (m2 ⋆ m3)
mlaw5 m1 m2 m3 = sym (m-*assoc m1 m2 m3)

mlaw611111 : {n m : ℕ}(xss : m × n)
  →  multiply (id {m}) xss ≡ xss
mlaw611111 xss = m-one* xss

mlaw71 : {n m : ℕ}(xss : m × n)
  →  multiply xss (id {n}) ≡ xss
mlaw71 xss = m-*one xss

mlaw8 : {m n k : ℕ}(m1 : k × n)(m2 : n × m)(m3 : n × m)
  → m1 ⋆ (m2 ⊹ m3) ≡ ((m1 ⋆ m2) ⊹ (m1 ⋆ m3))
mlaw8 m1 m2 m3 = m-*+distrib m1 m2 m3

mlaw9 : {m n k : ℕ}(m1 : n × m)(m2 : n × m)(m3 : m × k) → (m1 ⊹ m2) ⋆ m3 ≡ ((m1 ⋆ m3) ⊹ (m2  ⋆ m3))
mlaw9 m1 m2 m3 rewrite (sym (ml m1 m3)) | (sym (ml m2 m3)) | (sym (ml (m1 ⊹ m2) m3))  = m-+*distrib m1 m2 m3

mlaw7 : {n m k : ℕ}(xss : m × n)
  →  xss  ⋆ (null {n} {k}) ≡ null {m} {k}
mlaw7 {n} {m} {k} xss rewrite sym (ml xss (null {n} {k})) = m-*zero xss

mlaw12 : {n m k : ℕ}(xss : n × k)
  →  (null {m} {n}) ⋆ xss ≡ null {m} {k}
mlaw12 {n} {m} xss rewrite sym (ml (null {m} {n}) xss)  = m-zero* xss

mlaw1 : {m n k : ℕ}(m1 : n × m)(m2 : n × m)(m3 : m × k)  → ((m1 ⊹ m2) ⋆ m3) ≡ ((m1 ⋆ m3) ⊹ (m2 ⋆ m3)) 
mlaw1 m1 m2 m3 rewrite sym (ml m1 m3)
  | sym (ml m2 m3) 
  | sym (ml (m1 ⊹ m2)  m3) = m-+*distrib m1 m2 m3

mlaw2 : {m n k : ℕ}(m1 : k × n)(m2 : n × m)(m3 : n × m) →  m1 ⋆ (m2 ⊹ m3) ≡ ((m1 ⋆ m2) ⊹ (m1 ⋆ m3)) 
mlaw2 m1 m2 m3  = m-*+distrib m1 m2 m3

mlaw61 : {k l : ℕ}(m1 : l × k) →  m1 ≡ m1 ⊹ (null {l} {k})
mlaw61 m1 = sym (m-zero+ m1)

mlaw6op : {k l : ℕ}(m1 : l × k) → (null {l} {k}) ⊹ m1 ≡ m1
mlaw6op m1 = m-+zero m1

mlaw7op : {k l m : ℕ}(m1 : k × m) → (null {l} {k}) ⋆ m1 ≡ null
mlaw7op {k} {l} m1 rewrite sym (ml (null {l} {k}) m1 )= m-zero* m1

idlaw : {k l : ℕ}(m : l × k) → m ⋆ id ≡ m
idlaw m rewrite sym (ml m id) = m-*one m

idlaws : {k l : ℕ}(m : l × k) → id ⋆ m ≡ m
idlaws m rewrite sym (ml id m) =  m-one* m

idlaws1 : {k : ℕ}(m : 1 × k) → ((true ∷ []) ∷ []) ⋆ m ≡ m
idlaws1 m = idlaws m

plusidempotence1 : {n : ℕ} → (x : Vec Bool n)
  → zipWith _∨_ x x ≡ x
plusidempotence1 [] = refl
plusidempotence1 (true ∷ xs) = cong (_∷_ true) (plusidempotence1 xs)
plusidempotence1 (false ∷ xs) = cong (_∷_ false) (plusidempotence1 xs)

plusidempotence : {n m : ℕ}(xss : m × n) → xss ⊹ xss ≡ xss
plusidempotence [] = refl
plusidempotence (x ∷ xs) rewrite plusidempotence1 x = cong (_∷_ _) (plusidempotence xs)

plusnullvector : {k : ℕ}(xss : 1 × k) → ((replicate false ∷ []) ⊹ xss) ≡ xss 
plusnullvector xss = mlaw6op xss

plusnullvectorob : {k : ℕ}(xss : 1 × k) → ((xss ⊹ (replicate false ∷ []))) ≡ xss
plusnullvectorob xss = mlaw6 xss

nulllist : {A : Set}(xs : List A) → xs +++ [] ≡ xs
nulllist [] = refl
nulllist (x :: xs) = cong (_::_ _) (nulllist xs)

{-
joinlemma : ∀{n m k l}(m1 : m × n)(m2 : l × k) →  〈  (join m1 m2) 〉 ≡ join (〈 m1 〉) (〈 m2 〉)
joinlemma m1 m2 = joinlemma' m1 m2
-}

concatsup1111 :  {k l n : ℕ}(x : Vec Bool k)(y : Vec Bool n)(ys : n × l)(xs : k × l)
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

concatsup112 : {n k o : ℕ}(xs : n × k)(ys : o × k)(x : Vec Bool k)
  → map (λ x' → foldr _ _∨_ false (zipWith _∧_ x x')) (xs ++ ys)
        ≡ 
   (map (λ x' → foldr _ _∨_ false (zipWith _∧_ x x')) xs
    ++
   map (λ x' → foldr _ _∨_ false (zipWith _∧_ x x')) ys)
concatsup112 [] ys x = refl
concatsup112 (x ∷ xs) ys x' 
  = cong (_∷_ _) (concatsup112 xs ys x')

concatsup11 : {k l n o : ℕ}(os : l × k)(xs : k × n)(ys : k × o)
  → os ⋆ (xs ++++ ys) ≡ (os ⋆ xs) ++++ (os ⋆ ys)
concatsup11 [] xs ys = refl
concatsup11 {k} {suc l} (x ∷ xs) xs' ys rewrite concatsup111 xs' ys  
 |  concatsup112 (〈 xs' 〉) (〈 ys 〉) x = cong (_∷_ _) (concatsup11 {k} {l} xs xs' ys)




concatsup2121 : {l k : ℕ}(x d : Vec Bool l)(x' f : Vec Bool k)
  → (foldr _  _∨_ false
       (zipWith _∧_ (x ++ x') (d ++ f))) 
  ≡ 
  (foldr _ _∨_ false (zipWith _∧_ x d) ∨
        foldr _ _∨_ false (zipWith _∧_ x' f))
concatsup2121 [] [] x' f = refl
concatsup2121 (x ∷ xs) (d ∷ ds) x' f 
  rewrite law1 {x ∧ d}
  {foldr _ _+_ false (zipWith _∧_ xs ds)}
  {foldr _ _+_ false (zipWith _∧_ x' f)} 
  = cong (λ q → x ∧ d ∨ q) (concatsup2121 xs ds x' f)


concatsup2122 : {l k n : ℕ}(ds : k × l)(fs : k × n)(x : Vec Bool l)(x' : Vec Bool n)
  → map (λ x0 → foldr (λ _ → Bool) _∨_ false
         (zipWith _∧_ (x ++ x') x0))
      (zipWith _++_ ds fs) 
    ≡ zipWith _∨_ (map
       (λ x0 → foldr (λ _ → Bool)  _∨_ false 
         (zipWith _∧_ x x0)) ds)
      (map
       (λ x0 → foldr (λ _ → Bool)  _∨_ false 
         (zipWith _∧_ x' x0)) fs)
concatsup2122 [] [] x x' = refl
concatsup2122 (d ∷ ds) (f ∷ fs) x x'
  rewrite concatsup2121 x d x' f 
  | concatsup2122 ds fs x x' = refl


concat2132 : {l k n : ℕ}(x : Vec Bool k)(xs : k × n)(ys : k × l)
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

con-⊗-stack' : {l k m : ℕ}(as : 1 × l)(os : 1 × k)(xs : l × m)(ys : k × m)
  →  as ++++  os  ⋆  (xs ++ ys) ≡ (as ⋆ xs ⊹ os ⋆ ys)
con-⊗-stack' (x ∷ []) (x' ∷ []) xs' ys rewrite concatsup213 xs' ys
  with (〈 xs' 〉) | (〈 ys 〉) 
... | [] | [] = refl --refl
... | ds | fs rewrite concatsup2122 ds fs x x' =  refl --refl


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


concatsup212' : {l k m n : ℕ}(as : n × l)(os : n × k)(xs : l × m)(ys : k × m)
  → (as ++++ os) ⋆ (xs ++ ys) ≡ ((as ⋆ xs) ⊹  (os ⋆ ys))
concatsup212' (x ∷ zs) (x' ∷ qs) xs' ys rewrite concatsup213 xs' ys
  with (〈 xs' 〉) | (〈 ys 〉) 
... | [] | [] = cong (_∷_ _) (concatsup212' zs qs xs' ys)
... | ds | fs rewrite concatsup2122 ds fs x x' = cong (_∷_ _) (concatsup212' zs qs xs' ys)
concatsup212' [] [] xs' ys = refl


postulate con-⊗-stack : {k l m n : ℕ}(R : k × l)(S : k × m)(U : l × n)(V : m × n) → ⟦ R ∣ S ⟧ ⋆ ⟦ U / V ⟧ ≡ R ⋆ U ⊹ S ⋆ V










concatsup12 : {k l n m : ℕ}(a : l × k)(b : n × k)(c : k × m)
  → ((a ++ b) ⋆ c) ≡ (a ⋆ c ++ b ⋆ c)
concatsup12 [] b c = refl
concatsup12 (x ∷ xs) b c = cong (_∷_ _) (concatsup12 xs b c)



ht111 : (a : 1 × 1)(b : 1 × 1)
  → a ⋆ b ≡ (true ∷ []) ∷ []
  → a ≡ (true ∷ []) ∷ []
ht111 ((true ∷ []) ∷ []) ((x' ∷ []) ∷ []) p = refl
ht111 ((false ∷ []) ∷ []) ((x' ∷ []) ∷ []) ()

ht121 : (a : 1 × 1)(b : 1 × 1)
  → a ⋆ b ≡ (true ∷ []) ∷ []
  → b ≡ (true ∷ []) ∷ []
ht121 ((x' ∷ []) ∷ []) ((true ∷ []) ∷ []) p = refl
ht121 ((true ∷ []) ∷ []) ((false ∷ []) ∷ []) ()
ht121 ((false ∷ []) ∷ []) ((false ∷ []) ∷ []) ()






addPreColsLemma1 : {m k n : ℕ}(xs : n × k)
  → zipWith _∷_ (replicate false)
      (zipWith _++_ (replicate (replicate {_} {m} false)) xs) 
  ≡ zipWith _++_ 
    (replicate (false ∷ replicate {_} {m} false)) xs
addPreColsLemma1 [] = refl
addPreColsLemma1 {m} {k} {suc n} (x ∷ xs) = cong (_∷_ _) (addPreColsLemma1 {m} {k} {n} xs)


addPreColsLemma : {n k l : ℕ}(m : l × k)
  → (addPreCols m n) ≡ ((null {_} {n}) ++++ m)
addPreColsLemma {nzero} [] = refl
addPreColsLemma {suc n} {k} {nzero} [] with zipWith _∷_ [] (addPreCols {k} {nzero} [] n)
... | []  = refl
addPreColsLemma {nzero} {k} {suc l} (x ∷ xs) = cong (_∷_ x) (addPreColsLemma {nzero} {k} {l} xs)
addPreColsLemma {suc n} (x ∷ xs) rewrite addPreColsLemma {n} (x ∷ xs)
  | addPreColsLemma1 {n} xs = refl

{-
join++++11 : {k m : ℕ}(x x0 : Vec Bool k)(x' : Vec Bool m)
  → foldr _ _∨_ false
      (zipWith _∧_ (x ++ x') (x0 ++ replicate false)) ≡ 
  foldr _ _∨_ false (zipWith _∧_ x x0)
join++++11 [] [] [] = refl
join++++11 [] [] (x ∷ xs) 
  rewrite join++++11 [] [] xs 
  | law11 {x} = refl
join++++11 (x ∷ xs) (x' ∷ xs') x0 
  rewrite join++++11 xs xs' x0 = refl

join++++13 : {k m : ℕ}(x : Vec Bool k)(x' x0 : Vec Bool m)
  → foldr _ _∨_ false
      (zipWith _∧_ (x ++ x') (replicate {_} {k} false ++ x0)) ≡ 
  foldr _ _∨_ false (zipWith _∧_ x' x0)
join++++13 [] [] [] = refl
join++++13 (x ∷ xs) [] [] rewrite join++++13 xs [] [] | law11 {x} = refl
join++++13 [] (x' ∷ xs) (x0 ∷ xs') = refl
join++++13 (x ∷ xs) (x' ∷ xs') (x0 ∷ xs0) rewrite join++++13 xs (x' ∷ xs') (x0 ∷ xs0) | law11 {x} = refl

join++++12 : {k m o : ℕ}(x : Vec Bool k)(x' : Vec Bool m)(td : o × m)
  → map
      (λ x0 →
         foldr _ _∨_ false
         (zipWith _∧_ (x ++ x') x0))
      (zipWith _++_ (replicate (replicate {_} {k} false)) td)
      ≡
      map
      (λ x0 →
         foldr _ _∨_ false (zipWith _∧_ x' x0))
      td
join++++12  x x' [] = refl
join++++12 {k}  x x' (x0 ∷ xs) rewrite join++++13 x x' x0 = cong (_∷_ _) (join++++12 x x' xs)

join++++1 : {k m n o : ℕ}(x : Vec Bool k)(x' : Vec Bool m)(tc : n × k)(td : o × m)
  → map
      (λ x0 →
         foldr _ _∨_ false
         (zipWith _∧_ (x ++ x') x0))
      (join tc td) ≡ 
  (map
       (λ x0 →
          foldr _  _∨_ false (zipWith _∧_ x x0))
       tc
       ++
       map
       (λ x0 →
          foldr _ _∨_ false (zipWith _∧_ x' x0))
       td)

join++++1 {k} x x' [] td rewrite addPreColsLemma {k} td = join++++12 x x' td 
join++++1 x x' (x0 ∷ xs) td rewrite join++++11 x x0 x' = cong (_∷_ _) (join++++1 x x' xs td)
-}

{-
join++++ : {k l m n o : ℕ}(a : l × k)(b : l × m)(c : k × n)(d : m × o)
  → (a ++++ b) ⋆ (join c d) ≡ (a ⋆ c) ++++ (b ⋆ d)
join++++ [] [] c d = refl
join++++ (x ∷ xs) (x' ∷ xs') c d  rewrite joinlemma c d 
  | join++++ xs xs' c d | join++++1 x x' (〈 c 〉) (〈 d 〉)  = refl
-}
