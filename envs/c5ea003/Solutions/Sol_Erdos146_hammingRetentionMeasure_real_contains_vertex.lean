-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_contains_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:30:42.66758+00:00
-- url     : https://prove2.me/submissions/6a499f9d-eb18-4355-a888-bd2a15a9cd80

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by
  classical
  simpa using
    hammingRetentionMeasure_real_contains_finset dimension {vertex}
