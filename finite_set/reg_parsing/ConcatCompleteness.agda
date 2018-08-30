
open import Algebra.CommSemiRings
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module ConcatCompleteness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec hiding (foldl) renaming (zipWith to devnull; map to devnull2)
open import Data.List  hiding (null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic
open import Data.Matrix
open import Data.Matrix.RingProperties

import NFA
open module nfalib = NFA ⅀ _≟_

open import Data.Bool.CommRingProperties
open import Algebra.CommSemiRings
open module bsr = CommSemiRing bsr

concatfunc : (nfa1 nfa2 : NFA) → (1 × _ → ⅀ → 1 × _)
concatfunc nfa1 nfa2 = (λ  v' a → v' ⋆
         (δ nfa1 a ++ null) ++++
         ((F nfa1 ⋆ I nfa2 ++ id) ⋆
          δ nfa2 a))

concatl31 : (x : Vec Bool 1)
  → (zipWith _∧_ x [ true ]) ≡ x
concatl31 (x ∷ []) rewrite law7 {x} = refl


concatl32 : (x : Vec Bool 1)
  → (foldr (λ _ → Bool)  _∨_ false x ∷ []) ≡ x
concatl32 (x ∷ []) rewrite law3 {x} = refl


concatl3 : {m : ℕ}(Fm : m × 1)
  → Fm ⋆ [ [ true ] ] ≡ Fm
concatl3 [] = refl
concatl3 (x ∷ xs) 
  rewrite concatl31 x 
  | concatl32 x = cong (_∷_ _) (concatl3 xs)


concatl51 : (x : Vec Bool 1)
  → (foldr _ _∨_ false
       (zipWith _∧_ x [ false ]) ∷ []) ≡ [ false ]
concatl51 (x ∷ []) rewrite law11 {x} = refl


concatl5 : {n : ℕ}(Fm : n × 1)
  → Fm ⋆ [ [ false ] ] ≡ null {_} {1}
concatl5 [] = refl
concatl5 (x ∷ xs) 
  rewrite concatl51 x = cong (_∷_ _) (concatl5 xs)


concatsup1 : (nfa1 nfa2 : NFA)(x : ⅀)(os : 1 × _)
  → (os ⋆ ((δ nfa1 x ++ null) 
    ++++ 
    ((F nfa1 ⋆ I nfa2 ++ id) ⋆ δ nfa2 x)))  
  ≡ 
  (os ⋆ (δ nfa1 x ++ null))
    ++++ 
  (os ⋆ (((F nfa1 ⋆ I nfa2) ⋆ (δ nfa2 x)) ++ δ nfa2 x))
concatsup1 nfa1 nfa2 x os 
  rewrite concatsup12
    (F nfa1 ⋆ I nfa2) 
    (id) 
    (δ nfa2 x)
 | idlaws (δ nfa2 x) 
 = concatsup11 os 
   (δ nfa1 x ++ replicate (replicate false))
   (((F nfa1 ⋆ I nfa2) ⋆ (δ nfa2 x)) ++ δ nfa2 x) 


concatsup211 : {l k : ℕ}(os : 1 × (l ✚ k))
  → os ≡ (take' l os) ++++ (init' {l} os)
concatsup211 {l} (os ∷ []) with splitAt (l) os
concatsup211 {l} (.(xs ++ ys) ∷ []) | (xs , ys , refl)  = refl


concatsup21 : {l k n : ℕ}(os : 1 × (l ✚ k))(xs : l × n)(ys : k × n)
  → (os ⋆ (xs ++ ys)) ≡ 
  ((take' l os ⋆ xs) ⊹  ((init' {l}  os) ⋆ ys))
concatsup21 {l} {k} os xs ys 
  = trans (cong (λ x → x ⋆ (xs ++ ys)) 
    (concatsup211 {l} {k} os)) 
    (concatsup212' (take' l os) (init' os) xs ys)


concatsup2 : (nfa1 nfa2 : NFA)(x : ⅀)(os : 1 × (∇ nfa1 ✚ ∇ nfa2))
  → (os ⋆ (((F nfa1 ⋆ I nfa2) ⋆ (δ nfa2 x)) ++ δ nfa2 x)) 
  ≡ (take' _ os ⋆ ((F nfa1 ⋆ I nfa2) ⋆ (δ nfa2 x))) ⊹ 
    (init' {∇ nfa1} os ⋆ δ nfa2 x)
concatsup2 nfa1 nfa2 x os 
  = concatsup21 os 
    ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x) (δ nfa2 x)


{- important lemma -}
concatsup : (nfa1 nfa2 : NFA)(os : 1 × ((∇ nfa1 ✚ ∇ nfa2)))
  → (v : ⅀)(vs : List ⅀)
  → run (nfa1 ○′ nfa2) (v :: vs) os 
    ⋆ (null {∇ nfa1} {1} ++ F nfa2)
  ≡ 
  run (nfa1 ○′ nfa2) vs 
  ((os ⋆ (δ nfa1 v ++ null)) ++++ 
    ((take' (∇ nfa1) os ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 v)) ⊹ (init' {∇ nfa1} os ⋆ δ nfa2 v)))
  ⋆ (null {∇ nfa1} {1} ++ F nfa2)
concatsup y y' os v vs  
 rewrite concatsup1 y y' v os
 | concatsup2 y y' v os = refl




concathelp11 : {k : ℕ}(x : Vec Bool k)
  → foldr _ _+_ false
       (zipWith _∧_ (replicate false) x) ≡ false
concathelp11 [] = refl
concathelp11 (x ∷ xs) = concathelp11 xs


concathelp1 : {k l : ℕ}(xs : l × k)
  → (map (λ x' → foldr _ _∨_ false 
         (zipWith _∧_ (replicate false) x'))
         xs)
  ≡ (replicate false)
concathelp1 [] = refl 
concathelp1 (x ∷ xs) rewrite concathelp11 x 
  = cong (_∷_ _) (concathelp1 xs)


concathelp2111 : (k l : ℕ)
  → zipWith _∷_ (replicate {_} {k} false) (replicate {_} {k} (replicate {_} {l} false)) ≡
      replicate (false ∷ replicate false) 
concathelp2111 nzero l = refl
concathelp2111 (suc n) l = cong (_∷_ _) (concathelp2111 n l)


concathelp211 : (k l : ℕ)
  → 〈 (replicate {_} {k} (replicate {_} {l} false)) 〉 
  ≡ null {l} {k}
concathelp211 nzero l = refl
concathelp211 (suc n) l rewrite concathelp211 n l 
  = concathelp2111 l n


concathelp2121 : {k : ℕ}(xs : Vec Bool k)
  → foldr _ _+_ false
      (zipWith _∧_ xs (replicate false)) ≡ false 
concathelp2121 [] = refl
concathelp2121 (x ∷ xs) 
  rewrite concathelp2121 xs 
  | law11 {x} = refl


concathelp212 : {k l : ℕ}(xs : Vec Bool k)
  → map (λ x → foldr _  _∨_ false (zipWith _∧_ xs x))
      (replicate {_} {l} (replicate {_} {k} false))
    ≡ replicate {_} {l} false
concathelp212 {nzero} {nzero} [] = refl
concathelp212 {nzero} {suc l} [] 
  = cong (_∷_ _) (concathelp212 {nzero} {l} [])
concathelp212 {suc k} {nzero} xs = refl
concathelp212 {suc k} {suc l} xs rewrite concathelp2121 xs 
  = cong (_∷_ _) (concathelp212 {suc k} {l} xs)


concathelp21 : {k l : ℕ}(st : 1 × k)
  → (st ⋆ replicate {_} {k} (replicate {_} {l} false))
    ≡ replicate {_} {l} false ∷ []
concathelp21 {k} {l} (xs ∷ [])
  rewrite concathelp211 k l
  | concathelp212 {k} {l} xs = refl


concathelp2 : (nfa1 nfa2 : NFA)(st : 1 × (∇ nfa2))(x : ⅀)
  → ((zipWith _++_ (replicate {_} {(∇ nfa1)} false ∷ []) st)
  ⋆ (δ nfa1 x ++ replicate (replicate false))) 
    ≡ (null {1} {∇ nfa1})
concathelp2 nfa1 nfa2 st x 
  rewrite con-⊗-stack
    (replicate {_} {(∇ nfa1)} false ∷ [])
    st
    (δ nfa1 x) 
    (replicate (replicate false))
  | concathelp1  〈 (δ nfa1 x) 〉
  | concathelp21 {∇ nfa2} {∇ nfa1} st
  | plusidempotence ((replicate {_} {∇ nfa1} false) ∷ []) 
  = refl


concathelp3 : (xss : 1 × 1) 
  → xss ⊹ [ [ true ] ] ≡ [ [ true ] ]
concathelp3 ((true ∷ []) ∷ []) = refl
concathelp3 ((false ∷ []) ∷ []) = refl


{- important lemma 2 -}
concathelp : (nfa1 nfa2 : NFA)(vs : List ⅀)(Iy' : 1 × (∇ nfa2))
  → run nfa2 vs Iy' ⋆ F nfa2 ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) vs ((null {1} {∇ nfa1}) ++++ Iy')
      ⋆ (null {∇ nfa1} {1} ++ F nfa2) ≡  [ [ true ] ]
concathelp nfa1 nfa2  [] st p1
  rewrite  con-⊗-stack
      (null {1} {∇ nfa1})
      st
      (null {∇ nfa1} {1})
      (F nfa2)
  | p1 =  
  concathelp3 ((map
       (λ x → foldr _ _∨_ false
          (zipWith _∧_ (replicate false) x))
       (〈 (replicate (false ∷ [])) 〉)) ∷ [])

concathelp nfa1 nfa2  (x :: xs) st p1 
  rewrite  concatsup12
    (F nfa1 ⋆ I nfa2) 
    (id) 
    (δ nfa2 x)
 | idlaws (δ nfa2 x)
 | concatsup11
   (zipWith _++_ (null {1} {∇ nfa1}) st)
   ((δ nfa1 x ++ null))
   (((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++ δ nfa2 x))
 | con-⊗-stack
   (replicate false ∷ [])
   st
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)
   (δ nfa2 x)
 | concathelp1 〈 ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x) 〉
 | plusnullvector (st ⋆ δ nfa2 x)
 | con-⊗-stack
   (replicate false ∷ [])
   st
   (δ nfa2 x)
   null
 | concathelp2 nfa1 nfa2 st x
 = concathelp nfa1 nfa2 xs (st ⋆ δ nfa2 x) p1


concatl4' : (nfa1 nfa2 : NFA)(us : List ⅀)(Iy : 1 × _)(Iy' : 1 × _)
  → run nfa1 us Iy ⋆ F nfa1 ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) us (Iy ++++ Iy')
      ⋆ (F nfa1 ++ null {∇ nfa2} {1}) ≡ [ [ true ] ]
concatl4' nfa1 nfa2 [] st st' p 
  rewrite con-⊗-stack st st' (F nfa1) (null {∇ nfa2} {1}) 
  | p  with (st' ⋆ (null {∇ nfa2} {1})) 
... | (true ∷ []) ∷ []  = refl
... | (false ∷ []) ∷ [] = refl
concatl4' nfa1 nfa2 (x :: xs) st st' p 
 rewrite concatsup11
    (st ++++ st')
    (δ nfa1 x ++ replicate (replicate false))
    ((F nfa1 ⋆ I nfa2 ++ id) ⋆ δ nfa2 x)
  | concatsup12
    (F nfa1 ⋆ I nfa2) 
    id
    (δ nfa2 x)
 | idlaws (δ nfa2 x)
 | con-⊗-stack st st'
   (δ nfa1 x)
   (replicate {_}  (replicate {_} {(∇ nfa1)} false))
 | concathelp21 {∇ nfa2} {∇ nfa1} st'  
 | plusnullvectorob (st ⋆ δ nfa1 x) 
 =  
 concatl4' nfa1 nfa2 xs (st ⋆ δ nfa1 x) 
     (st ++++ st' ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++ 
        δ nfa2 x)) p

concatl4 : (nfa1 nfa2 : NFA)(us : List ⅀)(Iy : 1 × _)(Iy' : 1 × _)
  → run nfa1 us Iy ⋆ F nfa1 ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) us (Iy ++++ Iy')
      ⋆ (F nfa1 ++ F nfa2) ≡ [ [ true ] ]
concatl4 nfa1 nfa2 [] st st' p 
  rewrite con-⊗-stack st st' (F nfa1) (F nfa2) 
  | p  with (st' ⋆ F nfa2) 
... | (true ∷ []) ∷ []  = refl
... | (false ∷ []) ∷ [] = refl
concatl4 nfa1 nfa2 (x :: xs) st st' p 
 rewrite concatsup11
    (st ++++ st')
    (δ nfa1 x ++ replicate (replicate false))
    ((F nfa1 ⋆ I nfa2 ++ id) ⋆
        δ nfa2 x)
  | concatsup12
    (F nfa1 ⋆ I nfa2) 
    id
    (δ nfa2 x)
 | idlaws (δ nfa2 x)
 | con-⊗-stack st st'
   (δ nfa1 x)
   (replicate {_}  (replicate {_} {(∇ nfa1)} false)) 
 | concathelp21 {∇ nfa2} {∇ nfa1} st' 
 | plusnullvectorob (st ⋆ δ nfa1 x) 
 = concatl4 nfa1 nfa2 xs (st ⋆ δ nfa1 x) 
   (st ++++ st' ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++
         δ nfa2 x)) p



concatmain211 : {l m : ℕ}(q : Vec Bool l)(x' z : Vec Bool m)(x : Vec Bool (l ✚ m) )
  → foldr _ _∨_ false
      (zipWith _∧_ (q ++ x') x) ≡ true
  → foldr _ _∨_ false
     (zipWith _∧_ (q ++ zipWith _∨_ x' z) x) ≡ true
concatmain211 q [] [] x p = p
concatmain211 [] (true ∷ xs) (x' ∷ xs') (false ∷ xs0) p 
  = concatmain211 [] xs xs' xs0 p
concatmain211 [] (true ∷ xs) (x' ∷ xs') (true ∷ xs0) p = refl
concatmain211 [] (false ∷ xs) (true ∷ xs') (true ∷ xs0) p = refl
concatmain211 [] (false ∷ xs) (true ∷ xs') (false ∷ xs0) p 
  = concatmain211 [] xs xs' xs0 p
concatmain211 [] (false ∷ xs) (false ∷ xs') (x0 ∷ xs0) p 
  = concatmain211 [] xs xs' xs0 p
concatmain211 (true ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (false ∷ xs1) p
  = concatmain211 xs (x' ∷ xs') (x0 ∷ xs0) xs1 p
concatmain211 (true ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (true ∷ xs1) p 
  = refl
concatmain211 (false ∷ xs) (x' ∷ xs') (x0 ∷ xs0) (x1 ∷ xs1) p 
  = concatmain211 xs (x' ∷ xs') (x0 ∷ xs0) xs1 p


concatmain212 :  {A : Set}(x y : A)
  → x ∷ [] ≡ y ∷ []
  → x ≡ y
concatmain212 x y p  = cong (λ q → head q) p


concatmain21 : {l m : ℕ}(xs : 1 × (l ✚ m))(q : Vec Bool l)(x z : Vec Bool m)
  → map (λ x' → foldr _ _∨_ false (zipWith _∧_ (q ++ x) x')) xs
        ≡ [ true ]
  → map (λ x' → foldr _ _∨_ false
         (zipWith _∧_ (q ++ zipWith _∨_ x z) x')) xs ≡ [ true ]
concatmain21 (x ∷ []) q x' z p1 
  rewrite concatmain211 q x' z x 
    (concatmain212  (foldr _ _∨_ false
    (zipWith _∧_ (q ++ x') x)) true p1) = refl


concatmain2 : (nfa1 nfa2 : NFA)(vs : List ⅀)(Fm : _ × 1)(xs :  1 × _)(st : 1 × (∇ nfa2))(0-mtrxm : 1 × (∇ nfa1))
  → run (nfa1 ○′ nfa2) vs (0-mtrxm ++++ st) ⋆ Fm ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) vs (0-mtrxm ++++ (st ⊹ xs)) 
    ⋆ Fm ≡ [ [ true ] ]
concatmain2 y y' [] f (z ∷ []) (x ∷ []) (q ∷ []) em 
  rewrite concatmain21 〈 f 〉 q x z 
    (concatmain212 (map 
      (λ x' → foldr _ _∨_ false (zipWith _∧_ (q ++ x) x'))
      〈 f 〉) [ true ] em) = refl
concatmain2 nfa1 nfa2 (x :: xs) f xs' st p em 
  rewrite concatsup12
    (F nfa1 ⋆ I nfa2) 
    id
    (δ nfa2 x)
 | idlaws (δ nfa2 x)
 | concatsup11 (zipWith _++_ p st)
   (δ nfa1 x ++ replicate (replicate false))
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++ δ nfa2 x)
 | concatsup11 (zipWith _++_ p (st ⊹ xs'))
   (δ nfa1 x ++ replicate (replicate false))
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++ δ nfa2 x)
 | con-⊗-stack p
   (st ⊹ xs')
   (δ nfa1 x)
   (replicate (replicate false))
 | concathelp21 {∇ nfa2} {∇ nfa1} (st ⊹ xs') 
 | plusnullvectorob (p ⋆ δ nfa1 x)
 | con-⊗-stack p (st ⊹ xs')
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)
   (δ nfa2 x)
 | mlaw1 st xs' (δ nfa2 x)
 | con-⊗-stack p st
   (δ nfa1 x) 
   (replicate (replicate false))
 | concathelp21 {∇ nfa2} {∇ nfa1} st 
 | plusnullvectorob (p ⋆ δ nfa1 x)
 | con-⊗-stack p st 
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)
   (δ nfa2 x) 
 | mlaw3 
   (p ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)) 
   (st ⋆ δ nfa2 x)
   (xs' ⋆ δ nfa2 x)
 =  concatmain2 nfa1 nfa2 xs f 
    (xs' ⋆ δ nfa2 x) 
    ((p ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x))
    ⊹ (st ⋆ δ nfa2 x)) (p ⋆ δ nfa1 x) em


concatmain2' : (nfa1 nfa2 : NFA)(vs : List ⅀)(Fm : _ × 1)(xs : 1 × (∇ nfa2))(st : 1 × (∇ nfa2))(0-mtrxm : 1 × (∇ nfa1))
  → run (nfa1 ○′ nfa2) vs (0-mtrxm ++++ st) ⋆ Fm ≡ [ [ true ] ] 
  → run (nfa1 ○′ nfa2) vs (0-mtrxm ++++ (xs ⊹ st)) ⋆ Fm 
    ≡ [ [ true ] ]
concatmain2' y y' vs Fm xs st 0-mtrxm p 
  rewrite mlaw4 xs st 
  = concatmain2 y y' vs Fm xs st 0-mtrxm p


concatmain112 : {k n : ℕ}(xs' : Vec Bool n)(x : Vec Bool k)(x' : Vec Bool _)
  → (foldr _ _∨_ false
       (zipWith _∧_ (replicate {_} {n} false ++ x) x') ∷ []) ∷ []
      ≡ [ [ true ] ]
  → (foldr _  _∨_ false
       (zipWith _∧_ (xs' ++ x) x') ∷ []) ∷ []
      ≡ [ [ true ] ]
concatmain112 [] x x' p = p
concatmain112 (true ∷ xs) [] (true ∷ xs') p = refl
concatmain112 (true ∷ xs) [] (false ∷ xs') p = concatmain112 xs [] xs' p
concatmain112 (false ∷ xs) [] (x' ∷ xs') p = concatmain112 xs [] xs' p
concatmain112 (true ∷ xs) (x' ∷ xs') (true ∷ xs0) p = refl
concatmain112 (true ∷ xs) (x' ∷ xs') (false ∷ xs0) p = concatmain112 xs (x' ∷ xs') xs0 p
concatmain112 (false ∷ xs) (x' ∷ xs') (x0 ∷ xs0) p = concatmain112 xs (x' ∷ xs') xs0 p



concatmain111 : {k n : ℕ}(x : Vec Bool k)(tf : 1 × _)(xs : Vec Bool n)
  → map (λ x0 → foldr _ _∨_ false
        (zipWith _∧_ (replicate {_} {n} false ++ x) x0))
     tf ∷ []
     ≡ [ [ true ] ]
  → map (λ x0 → foldr _ _∨_ false
         (zipWith _∧_ (xs ++ x) x0))
      tf ∷ [] ≡ [ [ true ] ]
concatmain111 x (x' ∷ []) xs' p = concatmain112 xs' x x' p


concatmain11 : {k l : ℕ}(st : 1 × k)(xs : 1 × l)(f : _ × 1)
  → (replicate {_} {l} false ∷ []) ++++ st ⋆ f 
  ≡ [ [ true ] ]
  → xs ++++ st ⋆ f ≡ [ [ true ] ]
concatmain11 (x ∷ []) ([] ∷ []) f p = p
concatmain11 (x ∷ []) ((x' ∷ xs) ∷ []) f p = concatmain111 x 〈 f 〉 (x' ∷ xs) p 


concatmain1 : (nfa1 nfa2 : NFA)(vs : List ⅀)(Fm : _ × 1)(xs : 1 × (∇ nfa1))(st : 1 × (∇ nfa2))
  → run (nfa1 ○′ nfa2) vs ((null {1} {∇ nfa1}) ++++ st)
       ⋆ Fm ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) vs (xs ++++ st) ⋆ Fm ≡ [ [ true ] ]
concatmain1 nfa1 nfa2 [] f xs st p = concatmain11 st xs f p
concatmain1 nfa1 nfa2 (x :: xs) f xs' st p 
  rewrite concatsup12
    (F nfa1 ⋆ I nfa2) 
    id
    (δ nfa2 x)
 | idlaws (δ nfa2 x)
 | concatsup11
   ((replicate {_} {∇ nfa1} false ∷ []) ++++ st)
   (δ nfa1 x ++ replicate (replicate false))
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++
        δ nfa2 x) 
 | con-⊗-stack 
   (replicate false ∷ [])
   st
   (δ nfa1 x)
   (replicate (replicate false)) 
 | concathelp1 〈 δ nfa1 x 〉
 | concathelp21 {∇ nfa2} {∇ nfa1} st
 | plusidempotence ((replicate {_} {(∇ nfa1)} false) ∷ []) 
 | concatsup11
   (zipWith _++_ xs' st)
   (δ nfa1 x ++ replicate (replicate false))
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x ++
        δ nfa2 x)
 | con-⊗-stack xs' st
   ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)
   (δ nfa2 x)
 | con-⊗-stack (replicate false ∷ []) st
     ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x)
     (δ nfa2 x)
 | concathelp1 〈 ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x) 〉
 | plusnullvector (st ⋆ δ nfa2 x) 
 = 
 concatmain1 nfa1 nfa2 xs f (xs' ++++ st ⋆
        (δ nfa1 x ++ replicate (replicate false)))
     ((xs' ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x))
        ⊹ (st ⋆ δ nfa2 x)) 
     (concatmain2' nfa1 nfa2 xs f  
      (xs' ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 x))
      (st ⋆ δ nfa2 x)
      (replicate false ∷ []) p)



concatmain : (nfa1 nfa2 : NFA)(vs : List ⅀)
  (xs : 1 × (∇ nfa1))(ys : 1 × (∇ nfa2))
  (Iy' : 1 × (∇ nfa2))
  → run (nfa1 ○′ nfa2) vs ((null {1} {∇ nfa1}) ++++ (Iy'))
      ⋆ (null {∇ nfa1} {1}  ++ F nfa2) ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) vs (xs ++++ (Iy' ⊹ ys))
      ⋆ (null {∇ nfa1} {1}  ++ F nfa2) ≡ [ [ true ] ]
concatmain nfa1 nfa2 vs xs ys st p1 = 
  concatmain1 nfa1 nfa2 vs 
   (replicate {_} {∇ nfa1} (false ∷ []) ++ F nfa2) 
   xs (st ⊹ ys)  
   (concatmain2 nfa1 nfa2 vs 
     (replicate {_} {∇ nfa1} (false ∷ []) ++ F nfa2) 
     ys st (null {1} {∇ nfa1}) p1)



th12 : {l n : ℕ}(a : 1 × (l ✚ n))(b : l × 1)
  → (a ⋆ (b ++ (null {n} {1}))) ≡ (((take' l a) ⋆ b) ⊹ (null {1} {1}))
th12 {l} {n} a b  
  rewrite concatsup21 a b (null {n} {1})
  | mlaw7 {n} {1} {1} (init' {l} {n} a) = refl


th11 : {k : ℕ}(a : 1 × k)(b : k × 1)
  → (a ⋆ b) ⊹ null {1} {1} ≡ [ [ true ] ]
  → a ⋆ b ≡ [ [ true ] ]
th11 a b p rewrite mlaw6 (a ⋆ b) = p



th1 : (nfa1 nfa2 : NFA)(us : List ⅀)(v : ⅀)
  → run (nfa1 ○′ nfa2) us ((I nfa1) ++++ null)
    ⋆ (F nfa1 ++ (null {∇ nfa2} {1})) ≡ [ [ true ] ]
  → (take' (∇ nfa1)
      (run (nfa1 ○′ nfa2) us ((I nfa1) ++++ null))
        ⋆ ((F nfa1 ⋆ I nfa2) ⋆ δ nfa2 v))
    ≡ I nfa2 ⋆ δ nfa2 v
th1 nfa1 nfa2 ys v p 
  rewrite th12 
    (run (nfa1 ○′ nfa2) ys ((I nfa1) 
      ++++ (replicate false ∷ [])))
    (F nfa1) 
  | mlaw6 (take' (∇ nfa1)
    (run (nfa1 ○′ nfa2) ys ((I nfa1) ++++ null))
      ⋆ F nfa1)
  | mlaw5
    (F nfa1)
    (I nfa2)
    (δ nfa2 v)
  | sym (mlaw5
    (take' (∇ nfa1)
      (run (nfa1 ○′ nfa2) ys ((I nfa1) ++++ null)))
    (F nfa1)
    (I nfa2 ⋆ δ nfa2 v)) 
  | p 
  | idlaws (I nfa2 ⋆ δ nfa2 v) = refl


plus2lemma0 : {k : ℕ}(u : List ⅀)(v : List ⅀)(stm : 1 × k)
  → (f : (1 × _) → ⅀ → (1 × _))
  → foldl f stm (u +++ v)
    ≡ foldl f (foldl f stm u) v
plus2lemma0 [] v stm f = refl
plus2lemma0 (x :: xs) v stm f = plus2lemma0 xs v (f stm x) f


plus-split : (nfa : NFA) (u v : String) 
  → run (nfa +′) (u +++ v) (I nfa) ⋆ F nfa 
    ≡ run (nfa +′) v (run (nfa +′) u (I nfa)) ⋆ F nfa
plus-split nfa u v rewrite plus2lemma0 u v 
    (I nfa) 
    (λ A x → A ⋆ ((id ⊹ F nfa ⋆ I nfa) ⋆ δ nfa x)) = refl


th2 : (nfa1 nfa2 : NFA)(us : List ⅀)(v : ⅀)(vs : List ⅀)
  → run nfa1 us (I nfa1) ⋆ F nfa1 ≡ [ [ true ] ]
  → run nfa2 (v :: vs) (I nfa2) ⋆ F nfa2 ≡ [ [ true ] ]
  → run (nfa1 ○′ nfa2) (us +++ v :: vs)
     ((I nfa1) ++++ null)
      ⋆ ((null {(∇ nfa1)} {1}) ++ F nfa2) ≡ [ [ true ] ]
th2 nfa1 nfa2 us v vs d f 
  rewrite plus2lemma0 us (v :: vs) 
    ((I nfa1) ++++ null) (concatfunc nfa1 nfa2)
  | concatsup nfa1 nfa2
    (run (nfa1 ○′ nfa2) us ((I nfa1) ++++ null))
    v vs 
  | th1 nfa1 nfa2 us v 
    (concatl4' nfa1 nfa2 us (I nfa1) null d) 
  = concatmain nfa1 nfa2 vs 
    (run (nfa1 ○′ nfa2) us ((I nfa1) ++++ null)
         ⋆ (δ nfa1 v ++ replicate (replicate false)))
    (init' {∇ nfa1}
      (run (nfa1 ○′ nfa2) us ((I nfa1) ++++ null)) 
      ⋆ δ nfa2 v) 
    (I nfa2 ⋆ δ nfa2 v) 
    (concathelp nfa1 nfa2 vs (I nfa2 ⋆ δ nfa2 v) f)



th311 : {k n : ℕ}(xs : Vec Bool (n ✚ k))(x0 : Vec Bool n)(x' : Vec Bool k)
  → (foldr _ _∨_ false
      (zipWith _∧_ (xs) (replicate {_} {n}  false ++ x')) ∷ [])∷ []
     ≡ [ [ true ] ]
  → (foldr _ _∨_ false
       (zipWith _∧_ (xs) (x0 ++ x')) ∷ []) ∷ []
      ≡ [ [ true ] ]
th311 {k} {nzero} xs [] x' p = p
th311 {k} {suc n} (true ∷ xs) (true ∷ xs') x0 p = refl
th311 {k} {suc n} (false ∷ xs) (true ∷ xs') x0 p = th311 xs xs' x0 p
th311 {k} {suc n} (x ∷ xs) (false ∷ xs') x0 p rewrite law11 {x} = th311 xs xs' x0 p


th31 : {l k : ℕ}(x :  Vec Bool (l ✚ k))(tb : 1 × k)(tc : 1 × l)
  →  map
    (λ x' → foldr _ _∨_ false (zipWith _∧_ x x'))
    (zipWith _++_  (null {1} {l}) tb) ∷ []
    ≡ [ [ true ] ]
  → map
      (λ x' → foldr _ _∨_ false (zipWith _∧_ x x'))
      (zipWith _++_ tc tb) ∷ []
      ≡ [ [ true ] ]
th31 {nzero} x xss ([] ∷ []) p = p
th31 {suc n} (x ∷ xs) (x' ∷ []) (x0 ∷ []) p = th311 (x ∷ xs) x0 x' p


th32 : (l : ℕ)
  → 〈 null {l} {1} 〉 ≡ (null {1} {l})
th32 nzero = refl
th32 (suc n) rewrite th32 n = refl

  
th3 : {k l : ℕ}(a : 1 × _)(b : k × 1)(c : l × 1)
  → a ⋆ (null {l} {1} ++ b) ≡ [ [ true ] ]
  → a ⋆ (c ++ b) ≡ [ [ true ] ]
th3 (x ∷ []) b [] p = p
th3 {k} {l} (x ∷ []) b c p
  rewrite concatsup213 c b 
  | concatsup213 (null {l} {1}) b 
  | th32 l = th31 x 〈 b 〉  〈 c 〉 p

