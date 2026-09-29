-- Prove2me | Theorems.Thm_SimpleGraph_bridge_removal_two_components
-- name    : SimpleGraph.bridge_removal_two_components
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:43.593978+00:00
-- url     : https://prove2.me/theorems/82b543fb-8339-449b-a9f2-fdea1f6cb1e3
-- title:
--   Removing a bridge from a connected finite graph produces exactly
-- statement:
--   Removing a bridge from a connected finite graph produces exactly
--   two connected components.
--
--   ```lean
--   theorem SimpleGraph.bridge_removal_two_components[Fintype V] [DecidableEq V]
--       [DecidableRel G.Adj] {v w : V}
--       (hconn : G.Connected) (hb : G.IsBridge s(v, w)) :
--       Fintype.card (G \ fromEdgeSet {s(v, w)}).ConnectedComponent = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/BridgeSplit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/BridgeSplit.lean#L57

-- Thm stub generated from Bridges/GraphTheory/BridgeSplit.lean
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

theorem SimpleGraph.bridge_removal_two_components[Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {v w : V}
    (hconn : G.Connected) (hb : G.IsBridge s(v, w)) :
    Fintype.card (G \ fromEdgeSet {s(v, w)}).ConnectedComponent = 2 := by sorry
