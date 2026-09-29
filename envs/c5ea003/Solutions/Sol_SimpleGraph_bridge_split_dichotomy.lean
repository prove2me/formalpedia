-- Prove2me | solution 1 for SimpleGraph.bridge_split_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:43:47.868257+00:00
-- url     : https://prove2.me/submissions/14161f1e-e0bc-4ec4-b486-a4a448a2bdb7

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
theorem solution{v w : V}
    (hconn : G.Connected) (_hb : G.IsBridge s(v, w)) (x : V) :
    (G \ fromEdgeSet {s(v, w)}).Reachable v x ∨
    (G \ fromEdgeSet {s(v, w)}).Reachable w x := by
  have h_ind : ∀ {u x : V}, G.Reachable u x →
      (G \ fromEdgeSet {s(v, w)}).Reachable v x ∨
      (G \ fromEdgeSet {s(v, w)}).Reachable w x ∨
      (G \ fromEdgeSet {s(v, w)}).Reachable u x := by
    intro u x
    rintro ⟨p⟩
    induction' p with u x p ih
    · exact Or.inr <| Or.inr <| SimpleGraph.Reachable.refl _
    · by_cases h : s(x, p) = s(v, w)
      · aesop
      · rename_i h₁ h₂
        exact h₂.imp id (Or.imp id (fun h => by
          exact SimpleGraph.Reachable.trans
            (SimpleGraph.Adj.reachable <| by aesop) h))
  cases h_ind (hconn v x) <;> aesop
