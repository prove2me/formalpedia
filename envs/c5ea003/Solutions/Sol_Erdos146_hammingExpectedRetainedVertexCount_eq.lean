-- Prove2me | solution 1 for Erdos146.hammingExpectedRetainedVertexCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:31:24.193643+00:00
-- url     : https://prove2.me/submissions/1ffd2e56-d9fe-4096-90b9-2a25e0c547a6

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_vertex

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold hammingExpectedRetainedVertexCount
  simp_rw [hammingRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring
