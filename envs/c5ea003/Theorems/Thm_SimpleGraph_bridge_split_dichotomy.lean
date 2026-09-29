-- Prove2me | Theorems.Thm_SimpleGraph_bridge_split_dichotomy
-- name    : SimpleGraph.bridge_split_dichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:37.806608+00:00
-- url     : https://prove2.me/theorems/812d0d55-2ade-46ea-9c30-9b7a3137f14d
-- title:
--   Every vertex in a connected graph with a bridge removed is reachable
-- statement:
--   Every vertex in a connected graph with a bridge removed is reachable
--   from one of the two bridge endpoints.
--
--   ```lean
--   theorem SimpleGraph.bridge_split_dichotomy{v w : V}
--       (hconn : G.Connected) (_hb : G.IsBridge s(v, w)) (x : V) :
--       (G \ fromEdgeSet {s(v, w)}).Reachable v x ∨
--       (G \ fromEdgeSet {s(v, w)}).Reachable w x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/BridgeSplit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/BridgeSplit.lean#L35

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

theorem SimpleGraph.bridge_split_dichotomy{v w : V}
    (hconn : G.Connected) (_hb : G.IsBridge s(v, w)) (x : V) :
    (G \ fromEdgeSet {s(v, w)}).Reachable v x ∨
    (G \ fromEdgeSet {s(v, w)}).Reachable w x := by sorry
