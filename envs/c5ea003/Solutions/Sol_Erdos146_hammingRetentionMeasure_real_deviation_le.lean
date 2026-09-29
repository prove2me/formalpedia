-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_deviation_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:28:38.226+00:00
-- url     : https://prove2.me/submissions/6154d731-aeeb-4064-a8e1-bd7b8cd95fb6

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.StarOrdered
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_Erdos146_hammingRetentionMeasure_isProbability
import Theorems.Thm_Erdos146_hammingRetentionMeasure_memLp_two

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (hammingRetentionMeasure_memLp_two dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (hammingRetentionMeasure dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal
