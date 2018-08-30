-- [1] Neumann, René. "A Framework for Verified Depth-First Algorithms." ATx/WInG@ IJCAR. 2012.
-- [2] Pottier, François. "Depth-first search and strong connectivity in Coq." Vingt-sixièmes journées francophones des langages applicatifs (JFLA 2015). 2015.

import init.data.fin

structure implicit_graph :=
(initial: ℕ)
(fanout: ∀ y : ℕ, ℕ → fin y)

def reach (graph : implicit_graph) (known := ∀ z, fin z) (toSee := ∀ t, fin t) : ∀ y, fin y :=
    -- if ∃ x, x ∈ toSee then
    --     ∀ y ∈ implicit_graph.fanout x
    --     reach graph (known ∪ x) (toSee ∪ target)
    sorry
.



-- Algorithm 1 Simple DFS
-- visited ← ∅
-- procedure DFS x
--     if x /∈ visited then
--         visited ← visited ∪ {x}
--         for all e ∈ succs x do
--             DFS e
-- DFS start

--Algorithm 2 Simple DFS with state augmentation
-- visited ← ∅; σ ← σ0
-- procedure DFS x
--      if cond σ then
--          if x /∈ visited then
--              visited ← visited ∪ {x}; σ ← action σ x
--              for all e ∈ succs x do
--                  DFS e
--          else
--              σ ← remove σ x
--          σ ← post σ x
-- 11: DFS start

theorem pp : ∀ p q, ∃ x, x → p ∧ x → q :=
begin
    intros, 
end

theorem pp1 : ∀ p q, ∃ x, (¬x ∨ p) ∧ (¬x ∨ q) :=
begin
    intros, 
end