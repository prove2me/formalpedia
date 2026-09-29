-- Prove2me | solution 1 for ToughP4.numComp_complete_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:32:11.462872+00:00
-- url     : https://prove2.me/submissions/75dbb30c-b71f-4a30-8902-0f3bc5178a8f

import Mathlib
import Definitions.Def_Bridges_MinimallyToughP4Free
open ToughP4 in
theorem solution {V : Type*} [Fintype V] (S : Finset V) :
    numComp (⊤ : SimpleGraph V) S ≤ 1 := by
  unfold numComp
  -- the complete graph stays complete on `Sᶜ`, so all its vertices are mutually reachable
  haveI : Subsingleton ((⊤ : SimpleGraph V).induce ((↑S : Set V)ᶜ)).ConnectedComponent := by
    constructor
    intro c₁ c₂
    induction c₁ using SimpleGraph.ConnectedComponent.ind with
    | h u =>
      induction c₂ using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        rw [SimpleGraph.ConnectedComponent.eq]
        by_cases huv : u = v
        · rw [huv]
        · apply SimpleGraph.Adj.reachable
          simp only [SimpleGraph.comap_adj, SimpleGraph.top_adj, Function.Embedding.coe_subtype]
          exact fun h => huv (Subtype.ext h)
  exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
