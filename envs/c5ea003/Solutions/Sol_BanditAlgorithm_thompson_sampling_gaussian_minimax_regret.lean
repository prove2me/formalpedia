-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_gaussian_minimax_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:29:02.475107+00:00
-- url     : https://prove2.me/submissions/734ff44a-3fd3-46f1-9715-045cc9244202

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Theorems.Thm_BanditAlgorithm_finite_gap_pull_bound_to_minimax
import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_bound
import Mathlib.Probability.Distributions.Gaussian.Fernique

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π → (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 2 ≤ n →
        banditRegret (gaussianBandit μvec) π n ≤
          C * Real.sqrt (k * n * Real.log n) := by
  obtain ⟨C, hC, hpull⟩ := gaussian_ts_suboptimal_pull_count_bound
  refine ⟨1 + 3 * C, by positivity, ?_⟩
  intro k _ μvec π hπ hμ n hn
  let ν := gaussianBandit μvec
  have hInt : ∀ i, Integrable id (ν.P i) := by
    intro i
    change Integrable id (gaussianReal (μvec i) 1)
    exact IsGaussian.integrable_id
  rw [bandit_regret_decomposition ν hInt π n]
  apply finite_gap_pull_bound_to_minimax hn
  · intro i
    have hmean (j : Fin k) : banditArmMean ν j = μvec j := by
      simp [ν, gaussianBandit, banditArmMean]
    have hgap_nonneg : 0 ≤ banditGap ν i := by
      rw [banditGap]
      exact sub_nonneg.mpr
        (le_ciSup (Finite.bddAbove_range (fun j ↦ banditArmMean ν j)) i)
    have hopt_le : banditOptimalMean ν ≤ 1 := by
      unfold banditOptimalMean
      apply ciSup_le
      intro j
      rw [hmean j]
      exact (hμ j).2
    have harmlow : 0 ≤ banditArmMean ν i := by
      rw [hmean i]
      exact (hμ i).1
    constructor
    · exact hgap_nonneg
    · rw [banditGap]
      linarith
  · intro i
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun h ↦ by positivity)
  · exact (bandit_canonical_occupation_identities ν hInt π n).2
  · exact hC.le
  · intro i hi
    exact hpull k μvec π hπ i hi n hn

end BanditAlgorithm
