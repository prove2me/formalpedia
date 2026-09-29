-- Prove2me | solution 1 for TriangularForest.card_edgeFinset_le_of_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:18:55.247366+00:00
-- url     : https://prove2.me/submissions/86b2df0b-0aa6-4ebb-a0a3-5eb74e1108a6

import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
open TriangularForest SimpleGraph Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G G₁ G₂ : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : G ≤ G₁ ⊔ G₂) :
    #G.edgeFinset ≤ #G₁.edgeFinset + #G₂.edgeFinset := by
  classical
  have hsub : G.edgeFinset ⊆ G₁.edgeFinset ∪ G₂.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases h he with h1 | h2
      · refine Finset.mem_union_left _ ?_
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact h1
      · refine Finset.mem_union_right _ ?_
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact h2
  calc #G.edgeFinset ≤ #(G₁.edgeFinset ∪ G₂.edgeFinset) := Finset.card_le_card hsub
    _ ≤ #G₁.edgeFinset + #G₂.edgeFinset := Finset.card_union_le _ _
