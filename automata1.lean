import init.data.set
import init.algebra.order

open set
open fin

universe u
class has_transition (α : Type u) := (δ : α → α → Prop)
def δ {α : Type u} [has_transition α] : α → α → Prop := has_transition.δ
local notation a `▸` b := δ a b

class has_labelled_transition (α β: Type u) := (ltr : α → β → α → Prop)
def ltr {α β : Type u} [has_labelled_transition α β] : α → β → α → Prop := has_labelled_transition.ltr
local notation a `-` s `->` b := ltr a s b


def toTransition {S : Type} {V : Type} : (S → V → S → Prop) → S → S → Prop
| t s₁ s₂ := ∃ v : V, t s₁ v s₂

def Label_trans  (S L : Type) := S × L × S → Prop 
def Label_state (S L: Type) := S × L → Prop

structure TransitionSystem (S : Type) :=
    (δ : S × S → Prop)

structure LTS (S V : Type) extends TransitionSystem S :=
    (L : Label_trans S V)

structure Buchi (S V : Type) extends LTS S V :=
    (I : set S) 
    (Acc : set S)

structure Kripke (S AP : Type) extends TransitionSystem S :=
    (I : set S)
    (L : Label_state S AP)


structure K2B {S AP : Type} (k : Kripke S AP) extends Buchi (option S) (set AP)  :=
    ( dH : ∀ s : option S, δ (none, s))
    ( iH : I = (set_of (λ x, x = none)) )
    ( AccH : ∀ s : option S, s ∈ Acc )
    ( lH : ∀ t : S, ∀ lbl : AP, k.L ⟨ t, lbl ⟩ → ∃ ll : set AP, lbl ∈ ll → ∃ s : option S, L ⟨ s, ll, t⟩ ) 

variables {α : Type} {β : Type}
theorem thm : ∀ k : Kripke α β, K2B k :=
begin
 intros, destruct k, sorry
end

def nn : ℕ × ℕ → Prop 
| (1, 2)  := true 
| _ := false

structure Automata (S : Type) extends TransitionSystem (S : Type) :=
    (v : Type) -- vocabulary
    (L : S × S → v → Prop) -- labelled transitions


#check (⟨ (⟨ nn ⟩ : TransitionSystem ℕ) , (λ x, x = 2 ∨ x = 3), nn ⟩ : Kripke ℕ ℕ) 


