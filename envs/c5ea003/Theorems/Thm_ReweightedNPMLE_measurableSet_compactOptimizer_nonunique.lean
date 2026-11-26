-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_compactOptimizer_nonunique
-- name    : ReweightedNPMLE.measurableSet_compactOptimizer_nonunique
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:07.448184+00:00
-- url     : https://prove2.me/theorems/5763c8f6-c044-4c27-b976-203c6964f312
-- title:
--   Borel measurability of nonuniqueness in compact optimization
-- statement:
--   Let $X$ be a topological space equipped with its Borel sigma-algebra, let $M$ be a compact metric space, and let $U:X\times M\to\mathbb R$ be continuous. Define
--   $$A(x)=\{\mu\in M:U(x,\nu)\le U(x,\mu)\text{ for every }\nu\in M\}.$$
--   Then the parameter set
--   $$\{x\in X:\exists\mu,\nu\in A(x),\ \mu\ne\nu\}$$
--   is Borel measurable. This detects the existence of two distinct maximizing points without selecting either maximizer as a measurable function of the parameter.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L54-L84

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

theorem ReweightedNPMLE.measurableSet_compactOptimizer_nonunique {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) :
    MeasurableSet {x | ∃ μ ν : M, (x, μ) ∈ compactOptimizerGraph U ∧
      (x, ν) ∈ compactOptimizerGraph U ∧ μ ≠ ν} := by sorry
