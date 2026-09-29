-- Prove2me | solution 1 for BanditAlgorithm.bandit_stopped_klDiv_le_expected_information
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:49:38.198652+00:00
-- url     : https://prove2.me/submissions/f7a11456-61de-41f2-8610-cbb0f1a1d1a9

import Theorems.Thm_BanditAlgorithm_klDiv_stopped_le_iSup_truncations
import Theorems.Thm_BanditAlgorithm_bandit_bounded_stopping_klDiv_le_expected_information

open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    @klDiv (ℕ → Fin k × ℝ) hτ.measurableSpace
        ((banditTrajMeasure ν π).trim hτ.measurableSpace_le)
        ((banditTrajMeasure ν' π).trim hτ.measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  refine (klDiv_stopped_le_iSup_truncations ν ν' π τ hτ hfinite).trans ?_
  refine iSup_le fun n ↦
    (bandit_bounded_stopping_klDiv_le_expected_information ν ν' π τ hτ n).trans ?_
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_right' ?_ _
  refine lintegral_mono fun ω ↦ ENNReal.tsum_le_tsum fun t ↦ ?_
  split_ifs with htrunc hfull
  · exact le_rfl
  · exact False.elim (hfull ⟨htrunc.1.trans_le (min_le_left _ _), htrunc.2⟩)
  · exact bot_le
  · exact le_rfl
