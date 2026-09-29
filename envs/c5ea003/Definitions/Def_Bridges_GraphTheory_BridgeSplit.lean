-- Prove2me | Definitions.Def_Bridges_GraphTheory_BridgeSplit
-- name    : Bridges_GraphTheory_BridgeSplit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:14.984677+00:00
-- url     : https://prove2.me/theorems/54b1e641-4e35-4752-83d7-0713253ecff5
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_BridgeSplit
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.BridgeSplit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/BridgeSplit.lean by skeleton subtraction
import Mathlib
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


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Bridge Endpoint Separation -/


/-! ### Bridge Splitting -/



/-! ### 2-Edge-Connectivity -/

/-- A graph is 2-edge-connected if it is connected and has no bridges. -/
def IsTwoEdgeConnected (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ e, ¬G.IsBridge e

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

end SimpleGraph


