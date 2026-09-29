-- Prove2me | solution 1 for BanditAlgorithm.bandit_asymptotic_ucb_finite_time_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-07-21T02:29:04.03704+00:00
-- url     : https://prove2.me/submissions/f6ed9ac4-5e1f-4c7a-ba49-804042340350

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_suboptimal_arm_expected_pull_count_bound

open MeasureTheory ProbabilityTheory Filter

theorem solution {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π)
    (n : ℕ) (ε : Fin k → ℝ)
    (hε : ∀ i, 0 < BanditAlgorithm.banditGap ν i →
      0 < ε i ∧ ε i < BanditAlgorithm.banditGap ν i) :
    BanditAlgorithm.banditRegret ν π n ≤
      ∑ i ∈ Finset.univ.filter
          (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
        BanditAlgorithm.banditGap ν i *
          (1 + 5 / (ε i) ^ 2 +
            2 / (BanditAlgorithm.banditGap ν i - ε i) ^ 2 *
              (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
                Real.sqrt (Real.pi *
                  Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1)) := by
  rw [BanditAlgorithm.bandit_regret_decomposition ν hν.1 π n]
  calc
    (∑ i, BanditAlgorithm.banditGap ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ) ∂
          (BanditAlgorithm.banditMeasure ν π n)) ≤
      ∑ i, BanditAlgorithm.banditGap ν i *
        (1 + 5 / (ε i) ^ 2 +
          2 / (BanditAlgorithm.banditGap ν i - ε i) ^ 2 *
            (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
              Real.sqrt (Real.pi *
                Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hgap_nonneg : 0 ≤ BanditAlgorithm.banditGap ν i := by
        change 0 ≤ BanditAlgorithm.banditOptimalMean ν -
          BanditAlgorithm.banditArmMean ν i
        exact sub_nonneg.mpr
          (Finite.le_ciSup
            (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i)
      by_cases hgap : 0 < BanditAlgorithm.banditGap ν i
      · exact mul_le_mul_of_nonneg_left
          (BanditAlgorithm.asymptotic_ucb_suboptimal_arm_expected_pull_count_bound
            hν hπ n i (ε i) hgap (hε i hgap).1 (hε i hgap).2)
          hgap_nonneg
      · have hzero : BanditAlgorithm.banditGap ν i = 0 :=
          le_antisymm (le_of_not_gt hgap) hgap_nonneg
        simp [hzero]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hgap : 0 < BanditAlgorithm.banditGap ν i
      · simp [hgap]
      · have hgap_nonneg : 0 ≤ BanditAlgorithm.banditGap ν i := by
          change 0 ≤ BanditAlgorithm.banditOptimalMean ν -
            BanditAlgorithm.banditArmMean ν i
          exact sub_nonneg.mpr
            (Finite.le_ciSup
              (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i)
        have hzero : BanditAlgorithm.banditGap ν i = 0 :=
          le_antisymm (le_of_not_gt hgap) hgap_nonneg
        simp [hgap, hzero]
