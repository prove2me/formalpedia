-- Prove2me | solution 1 for BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-07-18T21:47:13.704851+00:00
-- url     : https://prove2.me/submissions/d38cbe6f-e63e-42e2-aa21-72edd22befed

import Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_expected_pull_count_ceiling_bound
import Mathlib.Tactic.Linarith

/-!
Reduction of Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020),
Theorem 7.1, printed pp. 105--108 (PDF pp. 114--117). The imported theorem is
the substantive probability/UCB step, Eq. (7.10) after `c = 1/2`. This file
performs only the source's final rounding and reciprocal-horizon estimates.
-/

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 0 < k) {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < BanditAlgorithm.banditGap ν i) :
    ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
        ∂(BanditAlgorithm.banditMeasure ν π n) ≤
      3 + 16 * Real.log n / (BanditAlgorithm.banditGap ν i) ^ 2 := by
  let x : ℝ := 16 * Real.log n / (BanditAlgorithm.banditGap ν i) ^ 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hceil : (((⌈x⌉₊ : ℕ) : ℝ)) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx).le
  have hinv : 1 / (n : ℝ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hnR
  have hcore :=
    BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count_ceiling_bound
      hk hν hn hπ i hi
  change (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
      ∂(BanditAlgorithm.banditMeasure ν π n)) ≤ 3 + x
  calc
    (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
        ∂(BanditAlgorithm.banditMeasure ν π n)) ≤
        (((⌈x⌉₊ : ℕ) : ℝ)) + 1 + 1 / (n : ℝ) := by
          simpa [x] using hcore
    _ ≤ 3 + x := by linarith
