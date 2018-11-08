

structure automata :=
(S : Type)          -- the states are just a type
(V : Type)          -- the vocabulary is just a type
(I : set S)         -- the initial state is a set of states in S
(δ : S → V → set S)
(F : set S)         -- final states is a partion of S 

def dd : nat → nat → set nat 
| 0 1 := {1}
| 0 2 := {2}
| _ _ := {}

#check ( ⟨ ℕ, ℕ, {1}, dd, λ x, x=2 ⟩ : automata )
#check automata.mk ℕ ℕ {1, 2} dd (λ x, x=2)
#check { automata . V := ℕ, F := λ x, x=2, I := {1}, δ := dd, S := ℕ }

--def fini (n: ℕ) : set ℕ := { k | k < n }
--structure fin (n : nat) := (val : nat) (is_lt : val < n)

/-
To prove that a set X is finite we need a surjective function from
 {1..n} to X
-/
structure finite_structure {n : ℕ} (X : Type) := 
    (f : fin n → X)
    (pf : function.surjective f)
@[simp] def finite (X : Type) : Prop := ∃ n : ℕ, ∃ f : fin n → X, function.surjective f

class dfa extends automata :=
{finS : finite S}          -- the state set should be finite
{finV : finite V}           -- the vocabulary set should be finite
{oneI : ∃ x : S, I = {x}}     -- a DFA has only one start state
{det  : ∀ s : S, ∀ v : V, ∃ t : S, δ s v = {t} } -- a DFA is complete and deterministic

def dd1 : fin 3 → fin 2 → set (fin 3)  | _ _ := {⟨1, by {apply nat.lt_succ_of_le,apply nat.le_succ_of_le, apply nat.le_refl}⟩ }

theorem finfinite : ∀ n : ℕ, finite (fin n) := by {
    intros, rw finite,
    existsi n, existsi id, rw function.surjective,
    intros, induction b,
    simp, existsi (⟨ b_val, b_is_lt ⟩ : fin n), refl,  
}

def dfa0 := {
    dfa .
    S := fin 3, V := fin 2, I := { (⟨ 1, by {
        apply nat.lt_succ_of_le,
        apply nat.le_succ_of_le, 
        apply nat.le_refl} ⟩ : fin 3) }, F := λ x, x = 1, δ := dd1,

    finS := finfinite 3,
    finV := finfinite 2,

    oneI := by { simp, existsi (⟨ 1, _ ⟩  : fin 3), simp, intros, 
        {apply nat.lt_succ_of_le, apply nat.le_succ_of_le, apply nat.le_refl}}, 
    det  := by { intros, cases s, cases v, simp,  existsi (⟨ 1, _⟩ :fin 3), simp [dd1], 
    apply nat.lt_succ_of_le,apply nat.le_succ_of_le, apply nat.le_refl,
    }
}

#check { dfa . S := fin 3, V := fin 2, I := {2}, F := λ x, x = 1, δ := dd1 }

example : nat.lt 0 2 := by {
    apply nat.zero_lt_succ,
}

-- example state set
inductive states1 : Type
| s1 : states1
| s2 : states1
| s3 : states1


@[simp] def fintostates1 : fin 3 → states1 
| ⟨ 0, _ ⟩ := states1.s1
| ⟨ 1, _ ⟩ := states1.s2
| ⟨ 2, _ ⟩ := states1.s3 
| ⟨nat.succ (nat.succ (nat.succ _)), _⟩ := states1.s3 

theorem states1finite : finite (states1) := by {
    simp, existsi 3, existsi fintostates1, rw function.surjective, intros, cases b,
    existsi (⟨0, _⟩ : fin 3), simp, apply nat.zero_lt_succ,
    existsi (⟨1, _⟩ : fin 3), simp, apply nat.lt_succ_of_lt, apply nat.succ_le_succ, apply nat.le_refl,
    existsi (⟨2, _⟩ : fin 3), simp, apply nat.lt_succ_of_le, apply nat.le_refl,
}

-- example vocabulary set
inductive vocabulary1 : Type
| a : vocabulary1
| b : vocabulary1

@[simp] def fintovocabulary1 : fin 2 → vocabulary1 
| ⟨ 0, _ ⟩ := vocabulary1.a
| ⟨ 1, _ ⟩ := vocabulary1.b
| ⟨nat.succ (nat.succ _), _⟩ := vocabulary1.b

theorem vocabulary1finite : finite (vocabulary1) := by {
    simp, existsi 2, existsi fintovocabulary1, rw function.surjective, intros, cases b,
    existsi (⟨0, _⟩ : fin 2), simp, apply nat.zero_lt_succ,
    existsi (⟨1, _⟩ : fin 2), simp, apply nat.lt_succ_of_le, apply nat.le_refl
}

-- example transition relation
def rr :  states1 → vocabulary1 → set states1
| states1.s1 _ := {states1.s2}
| states1.s2 _ := {states1.s3}
| states1.s3 vocabulary1.a := {states1.s1}
| states1.s3 vocabulary1.b := {states1.s2}

-- example final set
def SX : states1 → Prop 
| states1.s3 := true 
| _ := false
def SY := set_of SX

def rrn : ℕ → vocabulary1 → set ℕ  | _ _ := {1}

def dfa1 := {
    dfa.
    S := states1,
    V := vocabulary1,
    I := {states1.s1},
    F := {states1.s2},
    δ := rr,
    
    finS := states1finite,
    finV := vocabulary1finite,
    oneI := by { simp, existsi states1.s1, refl },
    det  := by { simp, intros, cases s, cases v, simp [rr], 
        existsi states1.s2, refl,
        existsi states1.s2, refl,
        existsi states1.s3, refl,
        cases v, existsi states1.s1, refl, existsi states1.s2, refl}
}

def invariant_checking (S: Type) (p : S → Prop) : Prop := ∀ s : S, p s
