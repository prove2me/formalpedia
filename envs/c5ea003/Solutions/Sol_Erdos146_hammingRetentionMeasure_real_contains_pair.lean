-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_contains_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:30:01.099259+00:00
-- url     : https://prove2.me/submissions/c49b117c-a9a5-4d0e-90c4-29bc9106d9f6

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    hammingRetentionMeasure_real_contains_finset dimension {first, second}
