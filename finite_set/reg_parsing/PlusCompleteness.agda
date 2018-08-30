
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module PlusCompleteness (⅀ : Set)
         (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec hiding (zipWith ; map ; foldl)
open import Data.List hiding (null) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
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

-----------
run+ : (nfa : NFA)(s : List ⅀) → (1 × ∇ nfa) → 1 × ∇ nfa
run+ nfa  toks st  = 
   foldl (λ  v a → (v ⋆ (δ nfa a)) ⊹ 
          (v ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa a))) st toks

δl1 : {n : ℕ}(m : 1 × n)(Fm : n × 1)(Im : 1 × n)(δm : n × n)
  → m ⋆ ((id ⊹ (Fm ⋆ Im)) ⋆ δm) ≡ 
    (m ⋆ δm) ⊹ (m ⋆ ((Fm ⋆ Im) ⋆ δm))
δl1 a b c d
  rewrite mlaw1 id (b ⋆ c) d 
  | idlaws d 
  | mlaw2 a d ((b ⋆ c) ⋆ d) = refl


δl : (nfa : NFA)(m : 1 × (∇ nfa))(u : List ⅀)
  → run (nfa +′) u m
  ≡ run+ (nfa ) u m 
δl nfa m [] = refl
δl nfa m (x :: xs) 
  rewrite δl1  m (F nfa) (I nfa) (δ nfa x) 
  = δl nfa ((m ⋆ δ nfa x) ⊹
      (m ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa x))) xs

------



plus-weak11 : {k  : ℕ}(m1 : 1 × k)(m2 : 1 × k)(FmIm : k × k)(δm : k × k)
  → (((m1 ⊹ m2) ⋆ δm) ⊹ ((m1 ⊹ m2) ⋆ (FmIm ⋆ δm)))
        ≡ 
     ((m1 ⋆ δm) ⊹  (m1 ⋆ (FmIm ⋆ δm ))) ⊹ 
       (m2 ⋆ (δm ⊹ (FmIm ⋆ δm)))
plus-weak11 m1 m2 m3 m4 
  rewrite mlaw1 m1 m2 m4 
  with (m3 ⋆ m4) 
... | e 
  rewrite mlaw1 m1 m2 e 
  | mlaw2 m2 m4 e
  with (m1 ⋆ m4) | (m2 ⋆ m4) | (m1 ⋆ e) | (m2 ⋆ e) 
... | a | b | c | d 
  rewrite sym (mlaw3 a b (c ⊹ d))
  | mlaw4 b (c ⊹ d)
  | mlaw4 b d
  | sym (mlaw3 a c (d ⊹ b))
  | mlaw3 c d b = refl


plus-weak1 : (nfa : NFA)(xs : List ⅀)(m1 m2 : 1 × _)
  → run+ nfa xs (m1 ⊹ m2)
     ≡ run+ nfa xs m1 ⊹ run+ nfa xs m2
plus-weak1 nfa [] m1 m2 = refl
plus-weak1 nfa (x :: xs) m1 m2 
  rewrite plus-weak11 m1 m2
    (F nfa ⋆ I nfa)
    (δ nfa x) 
  | plus-weak1 nfa xs 
    ((m1 ⋆ δ nfa x) ⊹
      (m1 ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa x)))
    (m2 ⋆ (δ nfa x ⊹
         ((F nfa 
           ⋆ I nfa) ⋆ δ nfa x)))
  | mlaw2 m2 
    (δ nfa x)
    (F nfa ⋆ I nfa 
      ⋆ δ nfa x) = refl


plus-weak31 : (m3 : 1 × 1)
  →  id {1} ⊹ m3 ≡ id {1}
plus-weak31 ((true ∷ []) ∷ []) = refl
plus-weak31 ((false ∷ []) ∷ []) = refl


plus-weak3 : {k : ℕ}(m1 : 1 × k)(m2 : 1 × k)(m3 : k × 1)
  → m1 ⋆ m3 ≡ id {1}
  → (m1 ⋆ m3) ⊹ (m2 ⋆ m3) ≡ id {1}
plus-weak3 m1 (x ∷ []) [] prf 
  rewrite prf = refl
plus-weak3 m1 m2 xs prf 
  rewrite prf 
  | plus-weak31 (m2 ⋆ xs) = refl


plus-weak : (nfa : NFA)(u : String)(I : 1 × _)
  → run nfa u I ⋆ F nfa ≡ id {1}
  → run+ nfa u I ⋆ F nfa ≡ id {1}
plus-weak nfa [] sm prf = prf
plus-weak nfa (x :: xs) sm prf 
  rewrite plus-weak1 nfa xs (sm ⋆ δ nfa x) (sm ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa x)) 
  | mlaw1 
    (run+ (nfa ) xs (sm ⋆ δ nfa x))
    (run+ (nfa ) xs (sm ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa x)))
    (F nfa) 
  | plus-weak3 
     (run+ (nfa ) xs (sm ⋆ δ nfa x)) 
     (run+ (nfa ) xs (sm ⋆ ((F nfa ⋆ I nfa) ⋆ δ nfa x)))
     (F nfa) 
     (plus-weak nfa  xs ((sm ⋆ δ nfa x) ) prf) = refl


plus2lemma2 : {n : ℕ}(osm : 1 × n)(δm : n × n)(Fm : n × 1)(Im : 1 × n)
  → osm ⋆ Fm ≡ id {1}
  → (osm ⋆ ((id ⊹ (Fm ⋆ Im)) ⋆ δm)) ≡ (osm ⋆ δm) ⊹ (Im ⋆ δm)
plus2lemma2 osm δm Fm Im p 
  rewrite δl1 osm Fm Im δm 
  | mlaw5 Fm Im δm 
  | sym (mlaw5 osm Fm (Im ⋆ δm)) 
  | p 
  | idlaws (Im ⋆ δm) = refl


plus-fin1 : (nfa : NFA)(x : ⅀)
  → (I nfa ⋆ ((id ⊹ (F nfa ⋆ I nfa)) ⋆ δ nfa x))
    ≡ (I nfa ⋆ (δ nfa x)) ⊹ (((I nfa ⋆ F nfa) ⋆ I nfa) ⋆ (δ nfa x))
plus-fin1 nfa x 
  with I nfa | F nfa | δ nfa x
... | a | b | c 
  rewrite  δl1 a b a c
  | mlaw5 a b a 
  | mlaw5 a (b ⋆ a) c = refl



plus-fin4 : {n : ℕ}(m1 : 1 × n)(m2 : n × n)
  → (([ [ false ] ] ⋆ m1) ⋆ m2) ≡ null
plus-fin4 m1 m2 
  rewrite mlaw5 [ [ false ] ] m1 m2 
  | mlaw12 {1} {1} (m1 ⋆ m2)  = refl


plus2lemma7 : (nfa : NFA)(xs : List ⅀)(os : 1 × (∇ nfa))(Im : 1 × ((∇ nfa)))
  → run (nfa +′) xs Im ⋆ F nfa ≡ id {1}
  → run (nfa +′) xs (os ⊹ Im) ⋆ F nfa ≡ id {1}
plus2lemma7 nfa [] os st p 
  rewrite mlaw1 os st (F nfa) 
  | p with os ⋆ F nfa
plus2lemma7 nfa [] os st p | (false ∷ []) ∷ [] = refl
plus2lemma7 nfa [] os st p | (true ∷ []) ∷ []  = refl
plus2lemma7 nfa (x :: xs) os st p 
  rewrite mlaw1 os st 
    ((id ⊹ (F nfa ⋆ I nfa)) ⋆ δ nfa x)
  = plus2lemma7 nfa xs 
      (os ⋆ ((id ⊹ (F nfa ⋆ I nfa)) ⋆ δ nfa x)) 
      (st ⋆ ((id ⊹ 
        (F nfa ⋆ I nfa)) ⋆ δ nfa x)) p



plus-fin : (nfa : NFA)(u : String)(I' : 1 × (∇ nfa))
  → run (nfa +′) u (I nfa) ⋆ F nfa ≡ id {1}
  → I' ⋆  F nfa ≡ id {1}
  → run (nfa +′) u I' ⋆ F nfa ≡ id {1}
plus-fin nfa [] xs p1 p2 = p2
plus-fin nfa (x :: xs) os p1 p2
  rewrite plus2lemma2 os 
    (δ nfa x)
    (F nfa)
    (I nfa)
    p2 
  | plus-fin1 nfa x with (I nfa ⋆ F nfa) 
... | (true ∷ []) ∷ [] 
  rewrite mlaw5 (id {1})
    (I nfa) (δ nfa x)
  | idlaws ((I nfa) ⋆ (δ nfa x) )
  | plusidempotence ((I nfa ⋆ δ nfa x)) 
  | plus2lemma7 nfa xs 
    (os ⋆ δ nfa x) 
    (I nfa ⋆ δ nfa x) p1  = refl
... | (false ∷ []) ∷ [] 
  rewrite plus-fin4 (I nfa) (δ nfa x) 
  | mlaw6 ((I nfa ⋆ δ nfa x)) 
  | plus2lemma7 nfa xs 
    (os ⋆ δ nfa x) (I nfa ⋆ δ nfa x) p1  = refl



plus-weak-cor : (nfa : NFA)(u : String)
  → run nfa u (I nfa) ⋆ F nfa ≡ id {1}
  → run (nfa +′) u (I nfa) ⋆ F nfa ≡ id {1}
plus-weak-cor nfa u p 
  rewrite δl nfa (I nfa) u 
  = plus-weak nfa u (I nfa) p
