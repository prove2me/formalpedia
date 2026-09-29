-- Prove2me | solution 1 for Erdos146.hammingRetainedVertexCount_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:32:05.854721+00:00
-- url     : https://prove2.me/submissions/c9c2f8eb-c5d0-45e3-9809-ca934a915ea3

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_event_eq_sum

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem hammingRetentionMeasure_integral_event_indicator
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (∫ retained,
      (if retained ∈ event then (1 : ℝ) else 0)
        ∂hammingRetentionMeasure dimension) =
      (hammingRetentionMeasure dimension).real event := by
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  split_ifs <;> simp

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by
  classical
  unfold hammingRetainedVertexCount hammingExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact hammingRetentionMeasure_integral_event_indicator dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}
