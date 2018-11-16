-- Generalized Transition Relation
import system.io

namespace gtr

-- C - is a type capturing the set of possible configurations
-- F - is a type capturing the set of possible actions (possible steps)
-- E - is a type capturing the set of possible events emanating from steps
-- initial is the set of possible initial configurations
-- steps is a function from configuration to steps, 
--      - what steps are enabled in a given configuration
--      - where can we do from a given configuration
-- doStep is a function mapping the execution of a step in a configuration to a set of outcomes
--      - an outcome is characterised by the destination configuration along with the set of events generated during the step 
structure GTR {C : Type} {F : Type} {E : Type} :=
    (initial : set C)
    (steps : C → set F)
    (doStep : C → F → set ((set E) × C))

def identity {C : Type} {F : Type} {E : Type} (s : @GTR C F E) : @GTR C F E := 
⟨ s.initial, s.steps, s.doStep  ⟩

-- the pruning functions blocks the evolution in configurations satisfying a given predicate
def pruning {C : Type} {F : Type} {E : Type} 
    (pred : C → bool) (s : @GTR C F E) : @GTR C F E :=
⟨   s.initial,
    λ c, cond (pred c) ∅ (s.steps c), 
    s.doStep 
⟩ 
 
def asserting {C : Type} {F : Type} {E : Type} {R : Type}
    (pred : C → bool) (reaction : C → R) (base : @GTR C F E)
: (@GTR C F E) :=
 ⟨ 
    base.initial,
    λ c, 
        if (¬ pred c) then 
            -- the pred was violated here
            do
            --reaction c ,
            base.steps c
            
            
        else 
            base.steps c,
    base.doStep
⟩ 

variables {α β : Type}

def prod (s₁ : set α)  (s₂ : set β) : set (α × β) 
:= { x | ∀ a ∈ s₁, ∀ b ∈ s₂, x = (a, b) }




def initialized {C : Type} {F : Type} {E : Type} 
    (ini : set C) (base : @GTR C F E)
: (@GTR C F E) :=
⟨ ini, base.steps, base.doStep ⟩ 

def compose{C : Type} {F: Type} {E: Type} {X:Type}
    (base: @GTR C F E)
    (initial: set X)
    (next: C×X → X)
: (@GTR (C×X) F E) :=
⟨ 
    (prod (base.initial) initial),
    λ c, base.steps c.fst,
    {x | ∀ c : C×X, ∀ f : F, ∃ frd ∈ base.doStep c.fst f, 
                x = (frd.fst, (frd.snd, next c)) }
⟩ 

namespace ga
def ga_state := list ℕ
def ga_initial : set ga_state := { [1, 2] }
def ga_steps : ga_state → set ℕ
| [1, 2] := {1}
| [2, 3] := {2, 3}
| s := {0}
def ga_doStep : ga_state → ℕ → set (set bool × ga_state) 
| [1,2] 1 := {({true}, [2, 3])}
| [2,3] 2 := {({true}, [2, 3])}
| [2,3] 3 := {({true}, [0, 0])}
| _ 0 := {({true}, [5, 0])}
| _ _ := {}

def gtr : GTR := ⟨ ga_initial, ga_steps, ga_doStep ⟩ 
end ga

#eval (λ x ∈ ga.ga_initial, ga.gtr.steps x) [1, 2] (by {simp [ga.ga_initial], sorry  }) 2



end gtr