-- inspired from https://github.com/UlfNorell/agda-summer-school/blob/OPLSS/lectures/Day1.agda

inductive Expr : Type
| elit (n : ℕ) : Expr
| ett : Expr 
| eff : Expr
| eless (a b : Expr) : Expr 
| eplus (a b : Expr) : Expr 
| eif (a b c : Expr) : Expr
.

inductive Value : Type
| nat  : ℕ → Value
| bool  : bool → Value
.

def getNat : Value → option ℕ 
| (Value.nat n) := some n
| (Value.bool b) := none

def getBool : Value → option bool
| (Value.nat n) := none
| (Value.bool b) := some b


def lookup : list ℕ → ℕ → option ℕ 
| [] _ := none
| (x::xs) i := if (i = 0) then some x else lookup xs (i-1).

#eval lookup [10, 20, 30] 2
#eval lookup [10, 20, 30] 4


namespace Expr

def eval : Expr → option Value
| (elit n) := some (Value.nat n)
| ett := some (Value.bool true)
| eff := some (Value.bool false)
| (eless e₁ e₂) := (λ n m, Value.bool (n < m)) 
                        <$> (getNat =<< eval e₁)
                        <*> (getNat =<< eval e₂)
| (eplus e₁ e₂) := (λ n m, Value.nat (n + m)) 
                        <$> (getNat =<< eval e₁)
                        <*> (getNat =<< eval e₂)
| (eif e₁ e₂ e₃) := eval e₁ --more here



#check (eif (elit 2) (elit 3) (elit 4))
end Expr