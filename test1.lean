
--debrujin indices, a fancy natural number
inductive IN {A : Type} (x : A) : list A → Type 
| zero : ∀ {xs}, IN (x::xs)
| succ : ∀ {y xs}, IN (x::xs) → IN (y::xs)

#check (IN.zero [1, 2, 3])
#check (IN.succ (IN.zero [1, 2, 3]))
#reduce (IN 2 [2 , 3])
#eval (IN (20) [2 , 3])

-- the environment which has elements of different types
-- at different indices, corresponding to the types in Γ 
inductive All {A : Type} (P : A → Type) : list A → Type 
| empty : All []
| cons : ∀ {x xs}, P x → All xs → All (x::xs)
open All

inductive Any {A : Type} (P : A → Prop) : list A → Type 
| zero : ∀ {x xs}, P x → Any (x::xs)
| succ : ∀ {x xs}, Any xs → Any (x::xs).

def IN' {A : Type} (x : A) (xs : list A) : Type := Any (λ y, eq x y) xs

def lookup : ∀ {A} { P : A → Type} {x xs}, IN' x xs → All P xs → P x 
| _ _ _ _ (Any.zero (eq.refl _)) (cons w ps)   := w
| _ _ _ _ (Any.succ i)           (cons w ps)   := lookup i ps

-- def lookup : ∀ {A} { P : A → Type} {x xs}, All P xs → IN x xs → P x 
-- | aType aP ax axs (All.cons w ps) (IN.zero) := w 
-- | aType aP ax axs (All.cons w ps) (IN.succ i) := lookup ps i.


inductive EType
| enat
| ebool

open EType
def Value : EType → Type 
| EType.enat := nat
| EType.ebool := bool

def Ctx := list EType
def Env : Ctx → Type := λ Γ, All Value Γ 

def Γ₀  : Ctx := ebool :: [].
def ρ₀  : Env Γ₀ :=  cons ff (empty Value).

def Γ₁  : Ctx := enat :: ebool :: [].
def ρ₁  : Env Γ₁ :=  cons (2:ℕ) (cons ff (empty Value)).