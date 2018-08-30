inductive Any {A : Type} (P : A → Prop) : list A → Type 
| zero : ∀ {x xs}, P x → Any (x::xs)
| succ : ∀ {x xs}, Any xs → Any (x::xs).

def IN' {A : Type} (x : A) (xs : list A) : Type := Any (λ y, eq x y) xs

--instance {A : Type} (x : A) (xs : list A): has_zero (IN' x (x::xs) ) := ⟨ Any.zero (eq.refl _) ⟩ 

inductive EType 
| enat 
| ebool
open EType

def Ctx := list EType
def Γ : Ctx :=  enat :: ebool :: [].

--instance : has_zero (IN' enat Γ) := ⟨ Any.zero (eq.refl _) ⟩

def in0 : IN' enat Γ := Any.zero (eq.refl _)
def in0' : IN' enat Γ := 0
def in1 : IN' ebool Γ := Any.succ (Any.zero (eq.refl _))
def in1' : IN' ebool Γ := 2

inductive All {A : Type} (P : A → Type) : list A → Type 
| empty : All []
| cons : ∀ {x xs}, P x → All xs → All (x::xs)
open All

def Value : EType → Type
| enat := nat
| ebool := bool
def Env : Ctx → Type := λ Γ, All Value Γ 

def ex_env : Env Γ := (cons (5:ℕ) (cons ff (empty Value))).