-- Prove2me | solution 1 for MarkovChainCLT.rhoMixingCoef_le_two_mul_sqrt_phiMixingCoef
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-04T22:42:05.101133+00:00
-- url     : https://prove2.me/submissions/43be70eb-ea8c-443b-9bab-f563158108b8

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_abs_covariance_le_two_mul_sqrt_phiMixingCoef
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory

namespace RhoPhiAux

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The zero pair is admissible in the supremum defining `rhoMixingCoef`. -/
theorem zero_mem_rhoSet (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) :
    (0 : ℝ) ∈ {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} := by
  refine ⟨0, (fun _ => 0), (fun _ => 0), measurable_const, measurable_const,
    MemLp.zero', MemLp.zero', ?_⟩
  simp [covariance]

end RhoPhiAux

open RhoPhiAux

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    rhoMixingCoef P Y n ≤ 2 * Real.sqrt (phiMixingCoef P Y n) := by
  refine csSup_le ⟨0, zero_mem_rhoSet P Y n⟩ ?_
  rintro r ⟨k, U, V, hU, hV, hU2, hV2, rfl⟩
  have hden : 0 ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hden with hzero | hpos
  · simp [← hzero]
  · rw [div_le_iff₀ hpos]
    exact MarkovChainCLT.abs_covariance_le_two_mul_sqrt_phiMixingCoef P Y n k U V hU hV hU2 hV2
