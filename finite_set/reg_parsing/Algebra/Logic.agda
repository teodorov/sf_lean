module Algebra.Logic where

open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_<_)
open import Algebra
open import Data.List
import Data.Nat.Properties as Nat
private module CS = CommutativeSemiring Nat.commutativeSemiring

subst2 : {A : Set} → (C : A → Set) → {a : A} → C a → {b : A} → a ≡ b → C b
subst2 C p refl = p

data Inspect' {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect' x

inspect' : {A : Set}(x : A) → Inspect' x
inspect' x = it x refl



Rel' : Set → Set₁
Rel' A = A → A → Set

data _<_ (m : ℕ) : ℕ → Set where
  <-base : m < suc m
  <-step : {n : ℕ} → m < n → m < suc n

lemm0 : {m : ℕ} →  0 < (suc m)
lemm0 {Data.Nat.zero} = <-base
lemm0 {suc m} = <-step lemm0

lemma01 : {m : ℕ} → 0 < (suc m) →  1 < (suc (suc m))
lemma01 {Data.Nat.zero} <-base = <-base
lemma01 {Data.Nat.zero} (<-step ())
lemma01 {suc n} (<-step y) = <-step (lemma01 y)

lemm1 : {m n : ℕ} →  m < n → (suc m) < (suc n)
lemm1 {Data.Nat.zero} {Data.Nat.zero} ()
lemm1 {Data.Nat.zero} {suc .0} <-base = <-base
lemm1 {Data.Nat.zero} {suc n} (<-step y) = lemma01 {n} (<-step y)
lemm1 {suc n} <-base = <-base 
lemm1 {suc m} {suc n} (<-step y) = <-step (lemm1 y)

lemm : {m n : ℕ} →  m < (suc n) → (suc m) < (suc (suc n))
lemm {Data.Nat.zero} p = lemm1 p
lemm {suc n} p = lemm1 p




module WF {A : Set} (_<_ : Rel' A) where
  data Acc (x : A) : Set where
    acc : (∀ y → y < x → Acc y) → Acc x

  Well-founded : Set
  Well-founded = ∀ x → Acc x

open WF _<_ public

<-ℕ-wf : WF.Well-founded _<_
<-ℕ-wf x = WF.acc (aux x)
  where
    aux : ∀ x y → y < x → WF.Acc _<_ y
    aux .(suc y) y <-base = <-ℕ-wf y
    aux .(suc x) y (<-step {x} y<x) = aux x y y<x

module Inverse-image-Well-founded { A B }
  (_<_ : Rel' B)(f : A → B) where
  _⊰_ : Rel' A
  x ⊰ y = f x < f y

  ii-acc : ∀ {x} → WF.Acc _<_ (f x) → WF.Acc _⊰_ x
  ii-acc (WF.acc g) = WF.acc (λ y fy<fx → ii-acc (g (f y) fy<fx))
  -- unwraps and then wraps it up again!

  ii-wf : WF.Well-founded _<_ → WF.Well-founded _⊰_
  ii-wf wf x = ii-acc (wf (f x))

module <-on-length-Well-founded { A } where
  open Inverse-image-Well-founded { List A } _<_ length public
  wf : WF.Well-founded _⊰_
  wf = ii-wf <-ℕ-wf