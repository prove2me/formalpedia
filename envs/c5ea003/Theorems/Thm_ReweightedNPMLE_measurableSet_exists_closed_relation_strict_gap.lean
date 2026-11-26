-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_exists_closed_relation_strict_gap
-- name    : ReweightedNPMLE.measurableSet_exists_closed_relation_strict_gap
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:00.764421+00:00
-- url     : https://prove2.me/theorems/bbb1b8c5-61e3-533d-a960-1bda2e809bfb
-- title:
--   Borel projection of a strict gap constrained by a closed relation
-- statement:
--   Let $X$ be a topological space with its Borel sigma-algebra, let $M$ be a compact topological space, and let $R\subset X\times M$ be closed. If $V:X\times M\to\mathbb R$ is continuous, then
--   $$\{x\in X:\exists\mu\in M,\ (x,\mu)\in R,\ V(x,\mu)>0\}$$
--   is Borel measurable. The relation may impose several simultaneous constraints; for example, $M$ can itself be a product of law spaces. The result requires a closed relation rather than a particular optimization representation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L140-L163

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

theorem ReweightedNPMLE.measurableSet_exists_closed_relation_strict_gap {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (R : Set (X × M)) (hR : IsClosed R)
    (V : X × M → ℝ) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ R ∧ 0 < V (x, μ)} := by sorry
