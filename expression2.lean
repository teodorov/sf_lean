-- inspired from https://github.com/UlfNorell/agda-summer-school/blob/OPLSS/lectures/Day1.agda

open nat 
inductive EType 
| enat 
| ebool
open EType

def Ctx := list EType

--debrujin indices, a fancy natural number
inductive IN {A : Type} : A → list A → Type 
| Zero : ∀ {x xs}, IN x (x::xs)
| Succ : ∀ {x y xs}, IN x (x::xs) → IN x (y::xs)
--notation a ` ∈ ` b := IN a b

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

inductive Expr : Ctx → EType → Type
| evar  {α Γ} :  IN' α Γ → Expr Γ α
| elit  {Γ} : ℕ → Expr Γ enat
| ett   {Γ} : Expr Γ ebool
| eff   {Γ} : Expr Γ ebool
| eless {Γ} (a b : Expr Γ enat) : Expr Γ ebool
| eplus {Γ} (a b : Expr Γ enat) : Expr Γ enat
| eif  {α Γ} (a : Expr Γ ebool) (b c : Expr Γ α) : Expr Γ α
open Expr

def Value : EType → Type
| enat := nat
| ebool := bool

def lookup : ∀ {A} { P : A → Type} {x xs}, IN' x xs → All P xs → P x 
| _ _ _ _ (Any.zero (eq.refl _)) (cons w ps)   := w
| _ _ _ _ (Any.succ i)           (cons w ps)   := lookup i ps

def Env : Ctx → Type := λ Γ, All Value Γ 

set_option eqn_compiler.lemmas false
def eval : ∀ {α Γ}, Env Γ →  Expr Γ α → Value α 
| _ _ env (evar x) := lookup x env
| _ _ env (elit n) := n
| _ _ env (ett) := true
| _ _ env (eff) := false
| _ _ env (eless e₁ e₂) := nat.lt (eval env e₁) (eval env e₂)
| _ _ env (eplus e₁ e₂) := nat.add (eval env e₁)  (eval env e₂)
| _ _ env (eif e₁ e₂ e₃) := if (eval env e₁ = true) then (eval env e₂) else (eval env e₃)


def Γ : Ctx :=  enat :: ebool :: [].
def ex_env : Env Γ := (cons (5:ℕ) (cons ff (empty Value))).

def ex_lit : Expr Γ enat := elit 2
def ex_ett : Expr Γ ebool := ett
def ex_eff : Expr Γ ebool := eff
def ex_expr0 : Expr Γ ebool := eless (elit 2) (elit 3)
def ex_expr1 : Expr Γ ebool := eif (eless (elit 2) (elit 3)) (ett) (eff)

def inxxx : Any (λ y, eq enat y) Γ := Any.zero (eq.refl _)
def zero : IN' enat Γ := Any.zero (eq.refl _)
def one : IN' ebool Γ := Any.succ (Any.zero (eq.refl _))
def ex_var0 : Expr Γ enat := evar (Any.zero (eq.refl _))
def ex_var1 : Expr Γ ebool := evar (Any.succ (Any.zero (eq.refl _)))


def ex_expr : Expr Γ enat := eif (evar one)  (evar zero)  (eplus (elit 4) (evar zero))
#reduce eval ex_env ex_expr
