open set

variable {U : Type}
variables W W' W'': Type

inductive act {W W' : Type}: Type
| x : act
| add : W → W' → act 
.

#check act.x
#check act.add 1 2


def action : W → W' := sorry.

def view : W → W' := sorry.
