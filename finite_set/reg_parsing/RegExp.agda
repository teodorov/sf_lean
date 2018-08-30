open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])


module RegExp (⅀ : Set)
            (_≟_ : Decidable (_≡_ {A = ⅀})) where


open import Relation.Nullary.Core
open import Relation.Nullary.Decidable
open import Data.Vec  hiding (foldl ; zipWith ; map ; _++_)
open import Data.List hiding (foldl ; drop ; zipWith ; map ; replicate ; foldr 
                             ; take ; reverse ; splitAt ; [_] ; null) 
                      renaming ( _∷_ to _::_)
open import Data.Nat  renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool

open import Algebra.CommSemiRings
open import Data.Matrix

import NFA
open module nfalib = NFA  ⅀ _≟_

data RegExp : Set where
   ε   : RegExp         
   ′_  : ⅀ → RegExp
   _∪_ : RegExp → RegExp → RegExp
   _₊  : RegExp → RegExp     
   _○_ : RegExp → RegExp → RegExp




data _◂_ :  String → RegExp → Set where
 empt : [] ◂ ε
 symb :  {x : ⅀} → (x :: []) ◂ (′ x)
 unionl : {u : String}{e₁ e₂ : RegExp} → (u ◂ e₁) → u ◂ (e₁ ∪ e₂)
 unionr : {u : String}{e₁ e₂ : RegExp} → (u ◂ e₂) → u ◂ (e₁ ∪ e₂)
 plus1 :  {u : String}{e : RegExp} → u ◂ e → u ◂ e ₊
 plus2 :  {u : String}{v : String}{e : RegExp} 
                                → u ◂ e → v ◂ e ₊ → (u ++ v) ◂ e ₊
 con : {u : String }{v : String}{e : RegExp}{e' : RegExp} 
                                → u ◂ e → v ◂ e' → (u ++ v) ◂ (e ○ e')
 



reg2nfa : RegExp → NFA
reg2nfa ε = record{
             ∇ = 1          ;
             δ   = λ x → null ;
             F   =  id        ;
             I   =  id   }
reg2nfa (′ x) = record {
         ∇ = 2 ;
         δ = λ y → if ⌊  x ≟ y  ⌋ 
                    then 
                      (false ∷ true ∷ [])  ∷ 
                      (false ∷ false ∷ []) ∷ [] 
                    else 
                      null ;
         F   = [ false ] ∷ [ true ] ∷ [] ;
         I   = (true ∷ false ∷ []) ∷ []  }
reg2nfa (e ∪ e₁) = reg2nfa e ∪′ reg2nfa e₁  
reg2nfa (e ₊) = (reg2nfa e) +′
reg2nfa (e ○ e₁) = reg2nfa e ○′ reg2nfa e₁  

