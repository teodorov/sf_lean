-- Christian Doczkal : https://www.ps.uni-saarland.de/extras/RLR-Coq/index.php
import init.data.set
import init.data.fin
open set
open nat decidable

-- example state set
inductive states1 : Type
| s1 : states1
| s2 : states1
| s3 : states1

-- example vocabulary set
inductive vocabulary1 : Type
| a : vocabulary1
| b : vocabulary1

-- example transition relation
def rr :  states1 → vocabulary1 → states1
| states1.s1 _ := states1.s2
| states1.s2 _ := states1.s3
| states1.s3 vocabulary1.a := states1.s1
| states1.s3 vocabulary1.b := states1.s2

-- example final set
def SX : states1 → Prop 
| states1.s3 := true 
| _ := false
def SY := set_of SX

structure Automata :=
    (S : Type) 
    (v : Type)
    (δ : S → v → S)

structure DFA extends Automata :=
    (initial : S)
    (final : set S)

#check (⟨states1, vocabulary1, rr⟩ : Automata) 
#check (⟨ ⟨states1, vocabulary1, rr⟩ , states1.s1, SY⟩ : DFA )

--variable A : DFA
def word (v : Type) := list v
def language (v : Type) := (word v) → Prop

#check word

def delta (A : DFA) : A.S → list A.v → A.S 
| p [] := p
| p (a::x) := delta (A.δ p a) x

def word1 := vocabulary1.a::vocabulary1.b::vocabulary1.b::[]
def dfa1 := (⟨ ⟨states1, vocabulary1, rr⟩ , states1.s1, SY⟩ : DFA )

#reduce dfa1.δ states1.s1 vocabulary1.a
#reduce delta dfa1 states1.s1 word1

section DFA_Acceptance
lemma delta_cons : ∀ d : DFA, ∀ p : d.S, ∀ a : d.v, ∀ x : list d.v,
    delta d (d.δ p a) x = delta d p (a::x) :=
by { intros, reflexivity }

lemma delta_cat : ∀ d : DFA, ∀ p : d.S, ∀ x : word d.v, ∀ y : list d.v,
    delta d p (x ++ y) = delta d (delta d p x) y :=
begin
    intros d p x y, 
    induction x generalizing p, 
    { simp [delta] } ,
    { simp [delta], rw ih_1 }
end

def dfa_accept (d: DFA) ( p : d.S ) ( w : list d.v ) := 
    (delta d p w) ∈ d.final 

def delta_s (d: DFA) ( w : list d.v ) := delta d d.initial w

--def dfa_lang (d: DFA) := [ pred x | dfa_accept d d.initial x ]
def lang (d : DFA) : list d.v → Prop 
| w  := delta_s d w ∈ d.final

def dfa_lang (d:DFA) : set (list d.v) := set_of (lang d)
def dfa_lang1 (d:DFA) : set (list d.v) := set_of (λ x, delta_s d x ∈ d.final)

lemma accept_nil : ∀ d : DFA, ∀ p : d.S, ∀ a : d.v, dfa_accept d p [] = (p ∈ d.final) :=
begin
    intros, reflexivity
end

lemma accept_cons : ∀ d : DFA, ∀ p : d.S, ∀ a : d.v, ∀ x : list d.v,
    dfa_accept d p (a::x) = dfa_accept d (d.δ p a) x :=
begin
    intros, reflexivity
end

lemma delta_lang : ∀ d : DFA, ∀ x : list d.v, (delta_s d x ∈ d.final) = (x ∈ dfa_lang d) :=
begin
    intros, reflexivity
end

end DFA_Acceptance


namespace last1
def last {T : Type} : T → list T → T
| x (x'::s') := last x' s'
| x _ := x
    
lemma last_cat : ∀ {T : Type} (x : T) (s1 s2 : list T), 
    last x (s1 ++ s2) = last (last x s1) s2 :=
begin
    intros,
    induction s1 generalizing x,
    {simp [last]},
    {simp [last], rw ih_1},
end
end last1

namespace last2
@[simp] def last {T : Type} : T → list T → T
| x (x'::s') := last x' s'
| x _ := x

lemma last_cat {T : Type} (x : T) (s1 s2 : list T) :
    last x (s1 ++ s2) = last (last x s1) s2 := 
by { induction s1 generalizing x; simp * }
end last2
