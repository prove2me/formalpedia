-- Prove2me | solution 1 for BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T16:11:02.168586+00:00
-- url     : https://prove2.me/submissions/be866128-3c07-49d3-98b5-6700cee4812e

import Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
import Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton

/-!
# Proposition 13, by the number of arms

The two cases are genuinely different and are proved separately.

* With **two or more arms** the plug-in objective `Ψ_i(μ, α) = min_{j≠i}(…)` has
  content, the rule is D-Tracking, and the settling time is integrable because
  the forced-exploration floor makes the empirical means consistent at a rate.
* With **one arm** there is nothing to identify: the arm space is a subsingleton,
  every trajectory plays the only arm, and the empirical allocation is exactly
  `1` from round one — only the mean needs an estimate.

The split is on `k` alone, which is known before any environment is presented,
so a single policy is still being exhibited: nothing here consults the answer.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem solution {k : ℕ} [NeZero k] :
    ∃ pol : BanditAlgorithm.BanditPolicy k,
      ∀ (μvec : Fin k → ℝ) (istar : Fin k),
        (∀ j, j ≠ istar → μvec j < μvec istar) →
        ∃ α : Fin k → NNReal,
          (∀ i, 0 < α i) ∧
          BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
              (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤ := by
  by_cases hk2 : 2 ≤ k
  · exact BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
      hk2
  · have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hk1 : ∀ i j : Fin k, i = j := by
      intro i j
      have hi : (i : ℕ) < k := i.isLt
      have hj : (j : ℕ) < k := j.isLt
      exact Fin.ext (by omega)
    exact
      BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_subsingleton
        hk1
