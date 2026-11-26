-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_exists_compactOptimizer_strict_gap
-- name    : ReweightedNPMLE.measurableSet_exists_compactOptimizer_strict_gap
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:48:16.249397+00:00
-- url     : https://prove2.me/theorems/d549be64-6597-4f99-bdde-58d6054ea0e8
-- title:
--   Borel measurability of a strict gap at some compact optimizer
-- statement:
--   Let $X$ be a topological space with its Borel sigma-algebra and let $M$ be a compact topological space. Suppose $U,V:X\times M\to\mathbb R$ are continuous. For $A(x)=\arg\max_{\mu\in M}U(x,\mu)$, the set
--   $$\{x\in X:\exists\mu\in A(x),\ V(x,\mu)>0\}$$
--   is Borel measurable. The criterion $V$ may represent a signed violation or a strict loss excess. No metrization of $M$ and no measurable choice of an optimizing point are required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L86-L108

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

theorem ReweightedNPMLE.measurableSet_exists_compactOptimizer_strict_gap {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (U V : X × M → ℝ) (hU : Continuous U) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < V (x, μ)} := by sorry
