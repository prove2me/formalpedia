-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_event_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:27:56.778143+00:00
-- url     : https://prove2.me/submissions/1f170082-ece5-49a2-bd6b-91f24c9efdc9

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.Real
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem solution
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (hammingRetentionMeasure dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  let support : Finset (Set (Bool × HammingWord dimension)) :=
    Finset.univ.filter (fun retained => retained ∈ event)
  have hsupport :
      (support : Set (Set (Bool × HammingWord dimension))) = event := by
    ext retained
    simp [support]
  calc
    (hammingRetentionMeasure dimension).real event =
        (hammingRetentionMeasure dimension).real support := by
      rw [hsupport]
    _ = ∑ retained ∈ support,
        (hammingRetentionMeasure dimension).real {retained} := by
      exact (MeasureTheory.sum_measureReal_singleton support).symm
    _ = ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
      rw [← Finset.sum_filter]
