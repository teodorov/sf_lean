
#check true ∧ false

section ltl
variable A : Type
def relation := A → A → Prop
variables 
    (state : Type) 
    (δ : relation state) 
    (label : Type) 
    (init_state : state -> Prop)
    (fair : label -> Prop). 

notation `LTL` := Sort 0

inductive next (φ : LTL) : LTL
inductive until (φ ψ: LTL) : LTL

reserve prefix `X` : 40
prefix X := next
notation `◯` φ := next φ 
notation φ ` U ` ψ := until φ ψ 

def releases (φ ψ : LTL) : LTL :=  ¬ (¬φ U ¬ψ)
notation φ ` R ` ψ := releases φ ψ

def eventually (φ : LTL) : LTL := true U φ
notation ` F ` φ := eventually φ
notation `◇` φ := eventually φ

def allways (φ : LTL) : LTL := false R φ
notation ` G ` φ := allways φ
notation `□` φ := allways φ

lemma distributivity_x_and : ∀ φ ψ, ◯ (φ ∨ ψ) = (◯ φ) ∨ (◯ ψ) := 
begin
intros, admit
end


end ltl