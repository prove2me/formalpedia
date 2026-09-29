-- Prove2me | solution 1 for K2UnionIndependentFree.zero_iff_bot
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:19.826784+00:00
-- url     : https://prove2.me/submissions/8c2637bb-a1c4-499d-abba-943e6bc469ce

-- Sol generated from Bridges/GraphTheory/K2UnionIndependentFree.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_K2UnionIndependentFree

/-!
# A structural lemma for `(K₂ ∪ kK₁)`-free graphs

The forbidden induced subgraph condition has a useful equivalent local form: after fixing
an independent `k`-set, the vertices with no neighbour in that set induce an edgeless graph.
This is one of the elementary reductions used in Hamilton-connectivity arguments for this
graph class.
-/

open Finset

open K2UnionIndependentFree

variable {V : Type*}










open K2UnionIndependentFree in
theorem solution(G : SimpleGraph V) :
    IsK2UnionK1Free G 0 ↔ G = ⊥ := by
  constructor
  · intro hfree
    ext u v
    simp only [SimpleGraph.bot_adj]
    constructor
    · intro hadj
      have := hfree hadj ∅ rfl (by simp) (by simp)
      contradiction
    · intro hv; contradiction
  · intro hG u v hadj
    simp [hG] at hadj
