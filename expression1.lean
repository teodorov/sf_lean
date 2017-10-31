-- inspired from https://github.com/UlfNorell/agda-summer-school/blob/OPLSS/lectures/Day1.agda
inductive EType 
| nat 
| bool
open EType

inductive Expr : EType → Type
| elit (n : ℕ) : Expr nat
| ett : Expr bool
| eff : Expr bool
| eless (a b : Expr nat) : Expr bool
| eplus (a b : Expr nat) : Expr nat
| eif {α} (a : Expr bool) (b c : Expr α) : Expr α
--| eif : ∀ {α}, Expr EType.bool → Expr α → Expr α → Expr α 
open Expr

def Value : EType → Type
| nat := nat
| bool := bool

def eval : ∀ {α}, Expr α → Value α 
| _ (elit n) := n
| _ ett := true
| _ eff := false
| _ (eless e₁ e₂) := nat.le (eval e₁) (eval e₂)
| _ (eplus e₁ e₂) := nat.add (eval e₁)  (eval e₂)
| _ (eif e₁ e₂ e₃) := if (eval e₁ = true) then (eval e₂) else (eval e₃)

