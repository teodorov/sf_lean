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