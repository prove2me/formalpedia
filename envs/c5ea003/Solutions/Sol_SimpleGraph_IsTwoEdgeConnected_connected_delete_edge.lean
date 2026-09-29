-- Prove2me | solution 1 for SimpleGraph.IsTwoEdgeConnected.connected_delete_edge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:42:46.189503+00:00
-- url     : https://prove2.me/submissions/9be964d3-83bc-42b6-bc2e-462a282df6bf

-- Sol generated from Bridges/GraphTheory/BridgeSplit.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_BridgeSplit
/-
# Bridge Splitting Theorem

This file proves that removing a bridge from a connected graph
produces exactly two connected components, and develops the theory
of 2-edge-connectivity.

## Main Results

* `SimpleGraph.bridge_removal_two_components` — removing a bridge gives 2 components
* `SimpleGraph.IsTwoEdgeConnected` — definition of 2-edge-connectivity
* `SimpleGraph.isTwoEdgeConnected_iff_forall_reachable_after_delete` — characterization

## References

* Diestel, R. *Graph Theory*, 5th edition, Springer, 2017.
-/


open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Bridge Endpoint Separation -/


/-! ### Bridge Splitting -/



/-! ### 2-Edge-Connectivity -/


/-
A 2-edge-connected graph remains connected after removing any single edge.
This is the defining property in terms of edge-fault tolerance.
-/

/-
Conversely, a connected graph where every single-edge deletion preserves
connectivity is 2-edge-connected.
-/

/-
A connected graph with no bridges has the property that every edge
lies on a cycle. This is the cycle characterization of 2-edge-connectivity,
using the bridge-cycle theorem from `BridgeCycle.lean`.
-/


open SimpleGraph in
theorem solution    (h2ec : G.IsTwoEdgeConnected) (e : Sym2 V) :
    (G \ fromEdgeSet {e}).Connected := by
  rcases h2ec with ⟨ hG, h ⟩;
  -- Since $e$ is not a bridge, removing $e$ from $G$ does not disconnect the graph.
  have h_connected : ∀ u v : V, G.Reachable u v → (G \ fromEdgeSet {e}).Reachable u v := by
    intro u v huv
    induction' huv with u v huv ih;
    induction' u with u v huv ih;
    · exact SimpleGraph.Reachable.refl _;
    · by_cases he : e = s(v, huv);
      · specialize h ( s(v, huv) ) ; simp_all +decide [ SimpleGraph.isBridge_iff ] ;
        exact h.trans ‹_›;
      · exact SimpleGraph.Reachable.trans ( SimpleGraph.Adj.reachable <| by aesop ) ‹_›;
  cases isEmpty_or_nonempty V <;> simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
  exact ⟨ hG.choose, fun w => h_connected _ _ ( hG.choose_spec w ) ⟩
