import init.data.set
import init.algebra.order

open set
open fin

universe u
class has_transition (α : Type u) := (δ : α → α → Prop)
def δ {α : Type u} [has_transition α] : α → α → Prop := has_transition.δ

local notation a `▸` b := δ a b

def toTransition {S V : Type} (S → V → S → Prop) : S → S → Prop := sorry 

structure TransitionSystem :=
    (S : Type)
    (δ : S → S → Prop)

structure Automata extends TransitionSystem :=
    (v : Type)
    (L : S → v → S → Prop)


