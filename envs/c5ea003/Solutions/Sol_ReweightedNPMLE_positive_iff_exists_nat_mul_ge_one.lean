-- Prove2me | solution 1 for ReweightedNPMLE.positive_iff_exists_nat_mul_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:04.049082+00:00
-- url     : https://prove2.me/submissions/41e75110-4b19-46e9-a3b5-74cd91e84f5b

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
open ReweightedNPMLE in
/-- A positive strict gap can be detected by a natural-number threshold. -/
theorem solution {t : ℝ} :
    0 < t ↔ ∃ j : ℕ, 1 ≤ ((j : ℝ) + 1) * t := by
  constructor
  · intro ht
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / t)
    refine ⟨j, ?_⟩
    have hle : 1 / t ≤ (j : ℝ) + 1 := by linarith
    exact (div_le_iff₀ ht).mp hle
  · rintro ⟨j, hj⟩
    by_contra ht
    have hnonpos : t ≤ 0 := not_lt.mp ht
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (j : ℝ) + 1 by positivity) hnonpos
    linarith
