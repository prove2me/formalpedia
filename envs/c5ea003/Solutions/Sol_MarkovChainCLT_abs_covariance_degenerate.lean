-- Prove2me | solution 1 for MarkovChainCLT.abs_covariance_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:23:09.621916+00:00
-- url     : https://prove2.me/submissions/a88892f0-1993-4814-ab68-54e44cebcd69

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_cov_abs_le_sqrt_var

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (hU2 : MemLp U 2 P) (hV2 : MemLp V 2 P)
    (hdeg : Var[U; P] = 0 ∨ Var[V; P] = 0) :
    |cov[U, V; P]| ≤ 2 * Real.sqrt (phiMixingCoef P Y n) *
      (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by
  have hcs := MarkovChainCLT.cov_abs_le_sqrt_var P U V hU2 hV2
  have hRHS_nonneg : 0 ≤ 2 * Real.sqrt (phiMixingCoef P Y n) *
      (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by positivity
  rcases hdeg with hU0 | hV0
  · rw [hU0] at hcs
    simp at hcs
    rw [hcs]
    simp
    exact hRHS_nonneg
  · rw [hV0] at hcs
    simp at hcs
    rw [hcs]
    simp
    exact hRHS_nonneg
