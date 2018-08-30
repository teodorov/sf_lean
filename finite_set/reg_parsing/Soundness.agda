
open import Algebra.CommSemiRings

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Core

module Soundness (⅀ : Set) (_≟_ : Decidable (_≡_ {A = ⅀}))  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.List hiding (foldl) renaming (drop to dropl; zipWith to zipWithl; map to mapl; replicate to replicatel; foldr to foldrl; take to takel; reverse to reversel; splitAt to splitAtl; _++_ to _+++_; _∷_ to _::_; [_] to devnull4)
open import Data.Nat hiding (_<_) renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.Logic

open import Data.Matrix
open import Data.Matrix.RingProperties

open import Data.Matrix.HelperTheorems



-- IMPORTING PROOFS --
import NFA
module nfalib = NFA ⅀ _≟_
open nfalib

import ConcatSoundness
open module consound = ConcatSoundness ⅀ _≟_

import PlusSoundness
open module plssound = PlusSoundness ⅀ _≟_

import UnionSoundness
open module unsound = UnionSoundness ⅀ _≟_

import TauSoundness
open module tausound = TauSoundness ⅀ _≟_

import EmptySoundness
open module empsound = EmptySoundness ⅀ _≟_

import RegExp 
open module regexp2 = RegExp ⅀ _≟_



mutual
 sound-mut : (s : String) → WF.Acc _⊰_ s  →  (e : RegExp) → (runNFA (reg2nfa (e ₊)) s) ≡ id {1} →  s ◂ (e ₊)
 sound-mut [] wf y p = plus1 (sound [] y p) 
 sound-mut (x :: []) wf y p rewrite (helper1 (I (reg2nfa y)) (F (reg2nfa y)) (δ (reg2nfa y) x))  = plus1 (sound (x :: []) y p)
 sound-mut (x :: x' :: xs) wf y p  
   with inspect' (run (reg2nfa y)  (x :: x' :: xs) (I (reg2nfa y)) ⋆ F (reg2nfa y))
 sound-mut (x :: x' :: xs) wf y p | it ((true ∷ []) ∷ []) prf1 = plus1 (sound (x :: x' :: xs) y prf1)
 sound-mut (x :: x' :: xs) (WF.acc wf) y p | it ((false ∷ []) ∷ []) prf1 rewrite (helper1 (I (reg2nfa y)) (F (reg2nfa y)) (δ (reg2nfa y) x))
   with plusmain (reg2nfa y) x x' xs (I (reg2nfa y)) p prf1 | plusmain-size (reg2nfa y) x x' xs p prf1
 ... | d1 , d2 , d3 , d4 , d5 | f rewrite (sym d3) = plus2 (sound (x :: d1) y d4) (sound-mut d2 (wf d2 f) y d5)


 sound : (u : String) →  (e : RegExp) → (runNFA (reg2nfa e) u) ≡ id {1} → u ◂ e

 {- single character -}
 sound [] (′ a) ()
 sound (x :: []) (′ a) run with inspect' (a ≟ x)
 sound (x :: []) (′ a) run | it (yes p) prf1 
   rewrite prf1 | p = symb {x}
 sound (x :: []) (′ a) run | it (no ¬p) prf1 
   rewrite prf1 with run
 ... | () 
 sound (x :: x' :: xs) (′ a) run with a ≟ x | a ≟ x' 
 sound (x :: x' :: xs) (′ a) run | (no ¬q) | (yes q)  
   rewrite τ_sound_main a xs with run
 ... | ()
 sound (x :: x' :: xs) (′ a) run | (no ¬q) | (no ¬z) 
   rewrite τ_sound_main a xs with run
 ... | ()
 sound (x :: x' :: xs) (′ a) run | (yes q) | (no ¬q) 
   rewrite τ_sound_main a xs with run
 ... | ()
 sound (x :: x' :: xs) (′ a) run | (yes q) | (yes z) 
   rewrite τ_sound_main a xs with run
 ... | ()

 {- concatenation -}
 sound u (e₁ ○ e₂) run with cons-split u (reg2nfa e₁) (reg2nfa e₂) (I (reg2nfa e₁)) run
 ... | d₁ , d₂ , d₃ , d₄ , d₅ rewrite d₃ = con {d₁} {d₂} (sound d₁ e₁ d₄) (sound d₂ e₂ d₅)


 {- plus -}
 sound [] (y ₊) run = plus1 (sound [] y run)
 sound (x :: []) (y ₊) p 
   rewrite 
   (helper1 (I (reg2nfa y)) (F (reg2nfa y)) (δ (reg2nfa y) x)) = plus1 (sound (x :: []) y p)
 sound (x :: x' :: xs) (y ₊) p 
   with inspect' (run (reg2nfa y)  (x :: x' :: xs) (I (reg2nfa y)) ⋆ F (reg2nfa y))
 sound (x :: x' :: xs) (y ₊) p | it ((true ∷ []) ∷ []) prf1 = plus1 (sound (x :: x' :: xs) y prf1)
 sound (x :: x' :: xs) (y ₊) p | it ((false ∷ []) ∷ []) prf1 rewrite 
   (helper1 (I (reg2nfa y)) (F (reg2nfa y)) (δ (reg2nfa y) x))
   with plusmain (reg2nfa y) x x' xs (I (reg2nfa y)) p prf1
 ... | d1 , d2 , d3 , d4 , d5 rewrite (sym d3) = plus2 (sound (x :: d1) y d4) (sound-mut d2 (wf d2) y d5)  


 {- eps  -}
 sound [] ε refl = empt
 sound (x :: xs) ε p rewrite (ε_sound_main xs) with p
 ... | ()

 {- union  -}
 sound s (y ∪ y') runprf rewrite
   unionmain (reg2nfa y) (reg2nfa y') s (I (reg2nfa y)) (I (reg2nfa y')) 
  | con-⊗-stack 
    (run (reg2nfa y) s (I (reg2nfa y)))
    (run (reg2nfa y') s (I (reg2nfa y')))
    (F (reg2nfa y))
    (F (reg2nfa y')) with inspect' (run (reg2nfa y) s (I (reg2nfa y)) ⋆ F (reg2nfa y))
 ... | it ((true ∷ []) ∷ []) prf1 
  rewrite prf1 = unionl (sound s y prf1)
 ... | it ((false ∷ []) ∷ []) prf1 
  rewrite prf1 
  | mlaw6op (run (reg2nfa y') s (I (reg2nfa y')) ⋆ F (reg2nfa y'))
  = unionr (sound s y' runprf)
  
