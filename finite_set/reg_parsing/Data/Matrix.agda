open import Algebra.CommSemiRings

module Data.Matrix  where

open import Data.Vec renaming (zipWith to devnull; map to devnull2)
open import Data.Nat renaming (zero to nzero; _+_ to _✚_; _*_ to _✖_)
open import Relation.Binary.PropositionalEquality

open import Data.Bool
open import Data.Product hiding (map) renaming (_×_ to _⊗_ )
open import Data.Bool.CommRingProperties

-- instantiating matrix library with Boolean semiring
open CommSemiRing bsr

infixl 8 _⋆_
infixl 7 _⊹_

{- matrix of m rows and n columns -}
_×_ : ℕ → ℕ → Set
n × m  = Vec (Vec R m) n
 
zipWith : ∀ {n} {A : Set} {B : Set} {C : Set} →
          (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

map :  {n : ℕ}{A B : Set} → (A → B) → Vec A n -> Vec B n
map f  []   =  []
map f (x ∷ xs)=  f x ∷ map f xs


{- matrix transposition -}
〈_〉  : {n m : ℕ} → m × n → n × m
〈 [] 〉 = replicate []
〈 xs ∷ xss 〉  = zipWith _∷_ xs 〈 xss 〉


{- make zero matrix  -}
null : {m n : ℕ} → m × n
null {n} {m} = replicate (replicate zero)



{- add matrices -}
_⊹_ : {n m : ℕ} → m × n → m × n → m × n
_⊹_ [] [] = []
_⊹_ (x ∷ xs) (y ∷ ys) = zipWith _+_ x y ∷ xs ⊹ ys 


{- matrix multiplication (two alternative definitions) -}

multRow : {n m : ℕ} → Vec R n → m × n → Vec R m
multRow v [] = []
multRow v (x ∷ xs) = 
  (foldr _ (_+_) zero (zipWith (_*_) v x )) ∷ multRow v xs


multiply : {n m k : ℕ} → m × n → n × k → m × k
multiply [] _ = []
multiply (x ∷ xs) m2 = multRow x 〈 m2 〉 ∷ multiply xs m2


multRow' : {n m : ℕ} → Vec R n → m × n → Vec R m
multRow' v xs = map (λ x → (foldr _ (_+_) zero (zipWith (_*_) v x )) ) xs

_⋆_ : {k l m : ℕ} → l × k → k × m → l × m
_⋆_ [] _ = []
_⋆_  {k} {suc l} {m} (rowA ∷ A) B = multRow' rowA 〈 B 〉  ∷ A ⋆  B


{- diagonal matrix -}
_◫_ : {n m k : ℕ} → k × n → k × m 
  → k × (n ✚ m)
xss ◫ yss = zipWith _++_ xss yss 

_++++_ : {n m k : ℕ} → k × n → k × m
  → k × (n ✚ m)
m1 ++++ m2 = m1 ◫ m2

addPreCol : {n m : ℕ} →  m × n → m × (suc n)
addPreCol xs = zipWith _∷_ (replicate zero) xs

addPreCols  : {n m : ℕ} →  m × n → (i : ℕ)  → m × (i ✚ n)
addPreCols mtrx nzero = mtrx
addPreCols {n} {m} mtrx (suc i) = addPreCol (addPreCols mtrx i)


{- slightly different variants of identity matrix, and proof that they are equal -}
id : {n : ℕ} → n × n
id {nzero} = []
id {suc n} = (one ∷ replicate zero) ∷ addPreCol id



{- joining matrices -}
take' : {k : ℕ}(l : ℕ)(os : 1 × (l ✚ k)) → 1 × l
take' l (x ∷ []) = (take l x) ∷ [] 

init' : {l k : ℕ}(os : 1 × (l ✚ k)) → 1 × k
init' {l} (x ∷ []) = (drop l x) ∷ []



{- blocks extension: (matrices as arrows) -}
i₁ : {n p : ℕ} → (n ✚ p) × n
i₁ {n} {p} = (id {n}) ++ (null {p} {n})

i₂ : {n p : ℕ} → (n ✚ p) × p
i₂ {n} {p} = (null {n} {p}) ++ id {p}

π₁ : {n p : ℕ} → n × (n ✚ p)
π₁ {n} {p} = zipWith _++_ (id {n}) (null {n} {p})

π₂ : {n p : ℕ} → p × (n ✚ p)
π₂ {n} {p} = zipWith _++_ (null {p} {n})  (id {p})


{-
⟦_/_⟧ : {n p m : ℕ} → (n × m) → (p × m) → (n ✚ p) × m
⟦_/_⟧ {n} {p} {m}  U V  = i₁ {n} {p} ⋆ U ⊹ i₂ {n} {p} ⋆ V

⟦_∣_⟧ : {k l m : ℕ} → (k × l) → (k × m) → k × (l ✚ m)
⟦_∣_⟧ {k} {l} {m} R S = R ⋆ π₁ ⊹ (S ⋆ π₂ {l})
-}

⟦_/_⟧ : {n p m : ℕ} → (n × m) → (p × m) → (n ✚ p) × m
⟦_/_⟧ {n} {p} {m}  U V  = U ++ V

⟦_∣_⟧ : {k l m : ℕ} → (k × l) → (k × m) → k × (l ✚ m)
⟦_∣_⟧ {k} {l} {m} R S = R ◫ S
