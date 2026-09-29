-- Prove2me | solution 1 for SimpleGraph.bridge_removal_two_components
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:46:42.960539+00:00
-- url     : https://prove2.me/submissions/533aa75a-bfed-441a-92ee-ba8a29523d2d

-- Sol generated from Bridges/GraphTheory/BridgeSplit.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_BridgeSplit
import Theorems.Thm_SimpleGraph_bridge_split_dichotomy
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
theorem solution[Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {v w : V}
    (hconn : G.Connected) (hb : G.IsBridge s(v, w)) :
    Fintype.card (G \ fromEdgeSet {s(v, w)}).ConnectedComponent = 2 := by
  rw [Fintype.card_eq_nat_card]
  rw [Nat.card_eq_two_iff']
  swap
  exact (G \ fromEdgeSet {s(v, w)}).connectedComponentMk v
  refine ⟨(G \ fromEdgeSet {s(v, w)}).connectedComponentMk w, ?_, ?_⟩
  · intro h
    exact hb.2 (by simpa [SimpleGraph.reachable_comm] using
      SimpleGraph.ConnectedComponent.eq.mp h)
  · rintro ⟨x⟩ hx
    have := bridge_split_dichotomy hconn hb x
    cases' this with h h
    · exact False.elim (hx (Quot.sound h.symm))
    · exact Quot.sound h.symm
