section kripke
variable A : Type
def relation := A → A → Prop
def tr := A → A → Prop

structure Frame := 
    (W : Type) -- the set of worlds
    (δ : relation W) -- the accessibility relation

structure kripke :=
    (frame : Frame)
    (atomic_propositions : Type)
    (label : frame.W → atomic_propositions → Prop)

end kripke


section ltl

inductive ltl : Type
| top : ltl
| bottom : ltl
| p : ltl
| negation : ltl → ltl
| disjunction : ltl → ltl → ltl
| next : ltl → ltl
| until : ltl → ltl → ltl
.

open ltl kripke
notation ` ¬ ` φ := negation φ
notation φ ` ∨ ` ψ := disjunction φ ψ

notation ` X ` φ := next φ 
notation ` ◯ ` φ := next φ 

notation φ ` U ` ψ := until φ ψ 

def releases (φ ψ : ltl) : ltl :=  ¬ (¬φ U ¬ψ)
notation φ ` R ` ψ := releases φ ψ

def eventually (φ : ltl) : ltl := top U φ
notation ` ◇ ` φ := eventually φ
notation ` F ` φ := eventually φ

def allways (φ : ltl) : ltl := bottom R φ
notation ` □ ` φ := allways φ
notation ` G ` φ := allways φ

def delta {model : kripke} :  model.frame.W → list model.frame.W → model.frame.W → Prop
| w [] n := model.frame.δ w n
| w (a::x) n := model.frame.δ w a → delta a x n


def world_satisfies {model : kripke} :  model.frame.W → ltl → Prop 
| _ top := true
| _ bottom := false
| _ p := true
| w (negation e) := ¬ (world_satisfies w e)
| w (disjunction e₁ e₂) := (world_satisfies w e₁) ∨ (world_satisfies w e₂)
| w (next e) := ∀ n : model.frame.W, model.frame.δ w n → (world_satisfies n e)
| w (e₁ U e₂) := ∃ n : model.frame.W,
                 ∀ path, delta w path n → (world_satisfies n e₂) → world_satisfies w e₁ ∧ (∀ x ∈ path, (world_satisfies x e₁))

def statisfies (model : kripke) (phi : ltl) : Prop :=
    ∀ w : model.frame.W, (world_satisfies w phi)




end ltl