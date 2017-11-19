-- https://www.youtube.com/watch?v=8upRv9wjHp0
inductive A 
| i : ℤ → A
| pred : A → A
| succ : A → A
| plus : A → A → A
| mult : A → A → A
.
open A
instance : has_one A := ⟨ A.i 1 ⟩ 
instance : has_add A := ⟨ A.plus ⟩ 

-- Natural semantics -- Big-step == Binary relation ↓ ⊆ A × ℤ 
inductive natsem_A : A → ℤ → Prop
| r1 : ∀ i : ℤ, natsem_A (A.i i) i
| r2 : ∀ e i, natsem_A e i → natsem_A (pred e) (i - 1)
| r3 : ∀ e i, natsem_A e i → natsem_A (succ e) (i + 1)
| r4 : ∀ e₁ e₂ i j, (natsem_A e₁ i) → (natsem_A e₂ j) → natsem_A (plus e₁ e₂) (i + j)
| r5 : ∀ e₁ e₂ i j, (natsem_A e₁ i) → (natsem_A e₂ j) → natsem_A (plus e₁ e₂) (i * j)

notation a ` ⇓ ` b := natsem_A a b

example : (plus 4 (succ 2)) ⇓ 7 := sorry

--Evaluator semantics of A
def eval : A → ℤ 
| (i x) := x
| (pred e) := (eval e) - 1
| (succ e) := (eval e) + 1
| (plus e₁ e₂) := (eval e₁) + (eval e₂)
| (mult e₁ e₂) := (eval e₁) * (eval e₂)

#reduce eval (plus 4 (succ 2))

-- SOS semantics of A == Binary relation ⟶ ⊆ A × A 
inductive sossem_A : A → A → Prop
--axioms
| sos1 : ∀ i,   sossem_A (pred (A.i i)) (A.i (i - 1))           -- i:ℤ 
| sos2 : ∀ i,   sossem_A (succ (A.i i)) (A.i (i + 1))
| sos3 : ∀ i j, sossem_A (plus (A.i i) (A.i j)) (A.i (i + j))
| sos4 : ∀ i j, sossem_A (mult (A.i i) (A.i j)) (A.i (i * j))
--contexts -- these contexts are known are the compatible closure
| sos05 : ∀ e₁ e₂,    sossem_A e₁ e₂ → sossem_A (pred e₁) (pred e₂)
| sos06 : ∀ e₁ e₂,    sossem_A e₁ e₂ → sossem_A (succ e₁) (succ e₂)
| sos07 : ∀ e₁ e₂ e₃, sossem_A e₁ e₂ → sossem_A (plus e₁ e₃) (plus e₂ e₃)
| sos08 : ∀ e₁ e₂ e₃, sossem_A e₁ e₂ → sossem_A (plus e₃ e₁) (plus e₃ e₂)
| sos09 : ∀ e₁ e₂ e₃, sossem_A e₁ e₂ → sossem_A (mult e₁ e₃) (mult e₂ e₃)
| sos10 : ∀ e₁ e₂ e₃, sossem_A e₁ e₂ → sossem_A (mult e₃ e₁) (mult e₃ e₂)

notation a ` ⟶ ` b := sossem_A a b

inductive sos_closure : A → A → Prop
| step : ∀ e₁ e₂, (e₁ ⟶ e₂) → sos_closure e₁ e₂
| reflexive : ∀ e, sos_closure e e
| transitive : ∀ e₁ e₂ e₃, sos_closure e₁ e₂ → sos_closure e₂ e₃ → sos_closure e₁ e₃

notation a ` ⟶* ` b := sos_closure a b

--I need something that extracts the value from A.i i in SOS
lemma natural_imp_sos : ∀ e i, (e ⇓ i) → (e ⟶* (A.i i)) := sorry
lemma sos_imp_natural : ∀ e i, (e ⟶* (A.i i)) → (e ⇓ i) := sorry

theorem natural_equivalent_sos : ∀ e i, (e ⇓ i) ↔ (e ⟶* (A.i i)) := 
begin
    intros, split; apply natural_imp_sos <|> apply sos_imp_natural
end

-- Reduction semantics of A
inductive axiom_redsem_A : A → A → Prop
--axioms
| red1 : ∀ i,   axiom_redsem_A (pred (A.i i)) (A.i (i - 1))           -- i:ℤ 
| red2 : ∀ i,   axiom_redsem_A (succ (A.i i)) (A.i (i + 1))
| red3 : ∀ i j, axiom_redsem_A (plus (A.i i) (A.i j)) (A.i (i + j))
| red4 : ∀ i j, axiom_redsem_A (mult (A.i i) (A.i j)) (A.i (i * j))

inductive ctx
| hole
| pred : ctx → ctx
| succ : ctx → ctx
| plus {e}: ctx → e → ctx | Plus {e}: e → ctx → ctx
| mult {e}: ctx → e → ctx | Mult {e}: e → ctx → ctx