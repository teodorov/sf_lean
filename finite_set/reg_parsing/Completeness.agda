open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module Completeness (⅀ : Set) (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl ; null) renaming 
 (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; 
  take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)

open import Data.Bool
open import Algebra.Logic
open import Data.Matrix
open import Data.Matrix.RingProperties

import NFA
module nfalib = NFA ⅀ _≟_
open nfalib

import RegExp
open module regexp = RegExp ⅀ _≟_

import ConcatCompleteness
open module concomp = ConcatCompleteness ⅀ _≟_

import PlusCompleteness
open module pluscomp = PlusCompleteness ⅀ _≟_

import UnionCompleteness
open module uncomp = UnionCompleteness ⅀ _≟_

import TauCompleteness
open module taucomp = TauCompleteness ⅀ _≟_


complete : (u : String) → (e : RegExp) → u ◂ e → (runNFA (reg2nfa e) u) ≡ id {1}

{- empty string  -}
complete .[] .ε empt = refl

{- tau -}
complete .(x :: []) .(′ x) (symb {x}) rewrite taulem x refl = refl  

{- union  -}
complete u (e₁ ∪ e₂) (unionl parseTree) with complete u e₁ parseTree
complete u (e₁ ∪ e₂) (unionl parseTree) | d 
  rewrite union-split 
    (reg2nfa e₁) (reg2nfa e₂) u 
    (I (reg2nfa e₁)) (I (reg2nfa e₂)) 
  | con-⊗-stack
    (run (reg2nfa e₁) u (I (reg2nfa e₁)))
    (run (reg2nfa e₂) u (I (reg2nfa e₂)))
    (F (reg2nfa e₁))
    (F (reg2nfa e₂))
  | d with 
  (run (reg2nfa e₂) u (I (reg2nfa e₂))) ⋆ F (reg2nfa e₂)  
... | (true ∷ []) ∷ [] = refl
... | (false ∷ []) ∷ [] = refl

complete u (e₁ ∪ e₂) (unionr parseTree) with complete u e₂ parseTree
complete u (e₁ ∪ e₂) (unionr parseTree) | d 
  rewrite union-split 
    (reg2nfa e₁) (reg2nfa e₂) u 
    (I (reg2nfa e₁)) (I (reg2nfa e₂)) 
  | con-⊗-stack 
    (run (reg2nfa e₁) u (I (reg2nfa e₁)))
    (run (reg2nfa e₂) u (I (reg2nfa e₂)))
    (F (reg2nfa e₁))
    (F (reg2nfa e₂)) 
  | d with 
  (run (reg2nfa e₁) u (I (reg2nfa e₁))) ⋆ F (reg2nfa e₁)
... | (true ∷ []) ∷ [] = refl --refl
... | (false ∷ []) ∷ [] = refl -- refl

{- plus -}
complete u (e ₊) (plus1 tree) with complete u e tree
complete u (e ₊) (plus1 tree) | d 
  rewrite δl (reg2nfa e) (I (reg2nfa e)) u = plus-weak nfa u (I nfa) d
  where nfa = reg2nfa e
complete .(u +++ v) (e ₊) (plus2 {u} {v} tree₁ tree₂) 
  with complete u e tree₁ | complete v (e ₊) tree₂
complete .(u +++ v) (e ₊) (plus2 {u} {v} tree e0) | d | f 
  rewrite  
    plus-split (reg2nfa e) u v
  = plus-fin nfa v
      (run (nfa +′) u (I nfa))
      f
      (plus-weak-cor nfa u d)
  where
    nfa = reg2nfa e

{- concat -}
complete .(us +++ []) (y ○ y') (con {us} {[]} y0 y1) with complete us y y0 | complete [] y' y1
... | d | f 
  rewrite plus2lemma0 us [] 
    (zipWith _++_ (I (reg2nfa y)) (replicate false ∷ [])) 
    (concatfunc (reg2nfa y) (reg2nfa y'))
  | f  
  | concatl3 (F (reg2nfa y)) 
  = concatl4 (reg2nfa y) (reg2nfa y') us (I (reg2nfa y)) 
    (replicate false ∷ [])  d
complete .(us +++ (v :: vs)) (y ○ y') (con  {us} {(v :: vs)} y0 y1) 
  with complete us y y0 | complete (v :: vs) y' y1
... | d | f with (I (reg2nfa y') ⋆ F (reg2nfa y')) 
... | (true ∷ []) ∷ [] 
  rewrite concatl3 (F (reg2nfa y)) 
  = th3 
    (run ((reg2nfa y) ○′ (reg2nfa y')) (us +++ v :: vs) 
     (⟦ (I (reg2nfa y)) ∣  (null) ⟧ ))
    (F (reg2nfa y')) 
    (F (reg2nfa y)) 
    (th2 (reg2nfa y) (reg2nfa y') us v vs d f)
... | (false ∷ []) ∷ [] 
  rewrite concatl5 (F (reg2nfa y)) 
  = th2 (reg2nfa y) (reg2nfa y') us v vs d f
