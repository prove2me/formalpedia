-- Prove2me | solution 1 for MarkovChainCLT.rhoMixingCoef_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:25:28.225843+00:00
-- url     : https://prove2.me/submissions/b23ce0a9-6812-4328-bd7d-8dda6bbabbcd

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_cov_abs_le_sqrt_var

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    rhoMixingCoef P Y n ≤ 1 := by
  unfold rhoMixingCoef
  apply csSup_le
  · -- nonempty: r=0 via k=0, U=V=0
    refine ⟨0, 0, fun _ => (0 : ℝ), fun _ => (0 : ℝ), measurable_const,
      measurable_const, memLp_const 0, memLp_const 0, ?_⟩
    simp
  · intro r hr
    obtain ⟨k', U, V, _, _, hU2, hV2, rfl⟩ := hr
    by_cases h0 : Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) = 0
    · rw [h0]
      simp
    · have hcs := MarkovChainCLT.cov_abs_le_sqrt_var P U V hU2 hV2
      have hpos : 0 < Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) :=
        lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rw [div_le_one hpos]
      exact hcs
