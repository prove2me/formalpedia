-- Prove2me | solution 1 for Erdos146.hammingExpectedRetainedEdgeCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:37:16.577646+00:00
-- url     : https://prove2.me/submissions/f3073b72-a870-402b-896e-f6162640eb31

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_pair
import Theorems.Thm_Erdos146_hammingWordEdge_sum_const

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeCount dimension radius =
      hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by
  classical
  have hpair (left right : HammingWord dimension) :
      (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained} =
        hammingRetentionProbability dimension ^ 2 :=
    hammingRetentionMeasure_real_contains_pair
      dimension (false, left) (true, right) (by simp)
  unfold hammingExpectedRetainedEdgeCount
  simp_rw [hpair]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hammingWordEdge_sum_const dimension radius
      (hammingRetentionProbability dimension ^ 2)
