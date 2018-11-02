
-- The notion of event is not part of the theory
-- We consider an event as being a set of events 

-- a set is a type S, thus an event(S) = S

import init.data.set
 

def spacetime (x y z t : nat) : Prop := true 

inductive event (S : Type)(t:nat) 
| evt : event
open event


--#check (evt nat 0) 1

--def precedesE (A B : event) := a  b

--def precedes (A B : event) : Prop := ∀ a : A, ∀ b : B , precedesE a b