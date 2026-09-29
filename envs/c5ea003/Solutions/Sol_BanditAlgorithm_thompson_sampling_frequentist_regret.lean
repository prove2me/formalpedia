-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_frequentist_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:53:53.87692+00:00
-- url     : https://prove2.me/submissions/ba77ec30-a441-44cd-b17b-143ca8ce614b

import Theorems.Thm_BanditAlgorithm_thompson_sampling_gaussian_asymptotic_regret
import Theorems.Thm_BanditAlgorithm_thompson_sampling_gaussian_minimax_regret

open MeasureTheory ProbabilityTheory Filter
open BanditAlgorithm

theorem solution :
    (∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π →
      Tendsto (fun n : ℕ ↦ banditRegret (gaussianBandit μvec) π n / Real.log n)
        atTop
        (nhds (∑ i ∈ Finset.univ.filter
            (fun i ↦ 0 < banditGap (gaussianBandit μvec) i),
          2 / banditGap (gaussianBandit μvec) i))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π → (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 2 ≤ n →
        banditRegret (gaussianBandit μvec) π n ≤
          C * Real.sqrt (k * n * Real.log n)) :=
  ⟨thompson_sampling_gaussian_asymptotic_regret,
    thompson_sampling_gaussian_minimax_regret⟩
