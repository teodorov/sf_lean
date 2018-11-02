

structure automata :=
(S : Type)          -- the states are just a type
(V : Type)          -- the vocabulary is just a type
(I : set S)         -- the initial state is a set of states in S
(δ : S → V → S)
(F : set S)         -- final states is a partion of S 

def dd : nat → nat → nat 
| 0 1 := 1
| 0 2 := 2
| _ _ := 0

#check ( ⟨ ℕ, ℕ, {1}, dd, λ x, x=2 ⟩ : automata )
#check automata.mk ℕ ℕ {1, 2} dd (λ x, x=2)
#check { automata . V := ℕ, F := λ x, x=2, I := {1}, δ := dd, S := ℕ }

--def fin (n: ℕ) : set ℕ := { k | k < n }

/-
To prove that a set X is finite we need a surjective function from
 {1..n} to X
-/
-- structure finite_structure {n : ℕ} (X : Type) := 
--     (f : fin n → X)
--     (pf : function.surjective f)
def finite (X : Type) : Prop := ∃ n : ℕ, ∃ f : fin n → X, function.surjective f

structure dfa extends automata :=
(finite_state : finite S)
(finite_vocab : finite V)
(one_start : ∀ x ∈ I, x = x)

def dd1 : fin 3 → fin 2 → fin 3  | _ _ := 2

example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from nat.zero_lt_succ 0,
exists.intro 1 h

theorem finfinite : ∀ n : ℕ, finite (fin n) := by {
    intros, rw finite,
    existsi n, existsi id, rw function.surjective,
    intros, induction b,
    simp, existsi (⟨ b_val, b_is_lt ⟩ : fin n), refl,  
}

#check {
    dfa .
    S := fin 3, V := fin 2, I := {2}, F := λ x, x = 1, δ := dd1,
    one_start := by {intros, refl},
    finite_vocab := finfinite 2,
    finite_state := finfinite 3,
}

#check {
    dfa .
    S := fin 3, V := fin 2, I := {2}, F := λ x, x = 1, δ := dd1,
    one_start := _,
    finite_vocab := _,
    finite_state := _,
}


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

#check {
    dfa .
    S := states1,
    V := vocabulary1,
    I := {states1.s1},
    F := SX,
    δ := rr,
    one_start := _,
    finite_vocab := _,
    finite_state := _,
}
