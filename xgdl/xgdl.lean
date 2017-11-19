import data.vector init.meta.tactic 

-- SOUNDNESS : every provable formula is valid
-- COMPLETENESS : every valid formula can be proven


inductive GDL : Type
| bot   : GDL
| a     : ℕ → GDL
| seq   : GDL → GDL  → GDL 
| alt   : GDL → GDL  → GDL 
| par   : GDL → GDL  → GDL 
| opt   : GDL → GDL 
| plus  : GDL → GDL 
| star  : GDL → GDL 
| iter  : GDL → ℕ → ℕ → GDL 
| arr (L : list ℕ) (j : { x : ℕ // 0 < x ∧ x ≤ L.length }) (i : { x : ℕ // 0 < x ∧ x ≤ j} ) : GDL
.
open GDL


#check alt (a 1) (a 2)

#check (arr [1, 2, 3, 4, 5] ⟨ 4, begin split; apply nat.le_add_left end ⟩ ⟨2, begin split; apply nat.le_add_left end⟩ )

meta def t_arrange_idx : tactic unit :=
`[ try { split }; apply nat.le_add_left]

#check (arr [1, 2, 3, 4, 5] ⟨ 5, by t_arrange_idx ⟩ ⟨2, by t_arrange_idx ⟩)
 

notation `⊥` := bot
notation `τ` := 0

inductive sos : GDL → ℕ → GDL → Prop
| atom : ∀ i, sos (a i) (i) (⊥)
| seq₁ : ∀ i C, sos (seq (a i) C) i C
| seq₂ : ∀ i C₁ C₂ C₃, C₁ ≠ (a i) → sos C₁ i C₂ → sos (seq C₁ C₃) i (seq C₂ C₃)  
| alt₁ : ∀ C₁ C₂, sos (alt C₁ C₂) τ (C₁)
| alt₂ : ∀ C₁ C₂, sos (alt C₁ C₂) τ (C₂)
| par₁ : ∀ i C₁ C₂ C₃, sos C₁ i C₂ → sos (par C₁ C₃) i (par C₂ C₃)
| par₂ : ∀ i C₁ C₂ C₃, sos C₁ i C₂ → sos (par C₃ C₁) i (par C₃ C₂)
| par₃ : ∀ C, sos (par ⊥ C) τ (C)
| par₄ : ∀ C, sos (par C ⊥) τ (C)
| opt  : ∀ C, sos (opt C) τ (alt ⊥ C)
| star : ∀ C, sos (star C) τ (opt (seq C (star C)))
| plus : ∀ C, sos (plus C) τ (seq C (star C))
| rep₁ : ∀ i j C, 0 < i ∧ i ≤ j → sos (iter C i j) τ (iter C (i-1) (j-1))
| rep₂ : ∀ i j C, i = 0 ∧ j > 0 → sos (iter C i j) τ (opt (seq C (iter C 0 (j-1))))
| rep₃ : ∀ i j C, i = 0 ∧ j = 0 → sos (iter C i j) τ ⊥
.

notation a `-` i `->` b := sos a i b
inductive sos_closure : GDL → GDL → Prop
| step : ∀ e₁ i e₂, (e₁ -i-> e₂) → sos_closure e₁ e₂
| reflexive : ∀ e, sos_closure e e
| transitive : ∀ e₁ e₂ e₃, sos_closure e₁ e₂ → sos_closure e₂ e₃ → sos_closure e₁ e₃

#print sos.atom 