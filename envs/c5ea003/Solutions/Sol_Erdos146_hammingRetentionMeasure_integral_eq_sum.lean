-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_integral_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:27:15.167639+00:00
-- url     : https://prove2.me/submissions/78dacee9-2418-4a2c-885b-7c54bee18fd2

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (hammingRetentionMeasure_integrable dimension observable))
