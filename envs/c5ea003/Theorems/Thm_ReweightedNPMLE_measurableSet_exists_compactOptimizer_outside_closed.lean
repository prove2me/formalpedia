-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_exists_compactOptimizer_outside_closed
-- name    : ReweightedNPMLE.measurableSet_exists_compactOptimizer_outside_closed
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:48:33.722907+00:00
-- url     : https://prove2.me/theorems/cf974b14-af8b-5796-825c-1c5a273db382
-- title:
--   Borel measurability of an optimizer outside a closed constraint set
-- statement:
--   Let $X$ carry its Borel sigma-algebra, let $M$ be a compact metric space, let $U:X\times M\to\mathbb R$ be continuous, and let $F\subset M$ be closed. Then
--   $$\{x:\exists\mu\in\arg\max_{\nu\in M}U(x,\nu),\ \mu\notin F\}$$
--   is Borel measurable. The closed set $F$ may be empty. In particular, whenever a structural property of candidate laws is represented by a closed subset, the existence of an optimizing law violating that property is a measurable parameter event.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L110-L138

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.measurableSet_exists_compactOptimizer_outside_closed {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) (F : Set M) (hF : IsClosed F) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} := by sorry
