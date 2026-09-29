-- Prove2me | solution 1 for BanditAlgorithm.etc_arm_expected_pull_count_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-07-21T02:24:07.699994+00:00
-- url     : https://prove2.me/submissions/40991dab-17dd-4822-80d7-bb4050ac5fd0

import Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_at_commit_time
import Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_step_bound

/-!
Source-faithful split of Lattimore--Szepesvari, *Bandit Algorithms* (CUP
2020), Section 6.1, Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102.
The two imported children are exactly the exploration identity (6.2) and the
post-commit recurrence (6.3).
-/

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {m : ℕ} (hm : 1 ≤ m) {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π)
    (i : Fin k) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π (m * k))
        (fun h : BanditAlgorithm.BanditHistory k (m * k) ↦
          (BanditAlgorithm.armPullCount i h : ℝ)) = m ∧
      ∀ r : ℕ, m * k ≤ r →
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π (r + 1))
            (fun h : BanditAlgorithm.BanditHistory k (r + 1) ↦
              (BanditAlgorithm.armPullCount i h : ℝ)) ≤
          MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π r)
            (fun h : BanditAlgorithm.BanditHistory k r ↦
              (BanditAlgorithm.armPullCount i h : ℝ)) +
            Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  exact ⟨
    BanditAlgorithm.etc_arm_expected_pull_count_at_commit_time hk hπ i,
    BanditAlgorithm.etc_arm_expected_pull_count_step_bound hk hν hm hπ i⟩
