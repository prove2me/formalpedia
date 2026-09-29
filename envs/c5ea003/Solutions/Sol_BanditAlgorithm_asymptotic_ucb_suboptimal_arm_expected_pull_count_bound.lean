-- Prove2me | solution 1 for BanditAlgorithm.asymptotic_ucb_suboptimal_arm_expected_pull_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-26T02:11:33.174023+00:00
-- url     : https://prove2.me/submissions/7ff1b08a-da9a-49f5-8795-788b0ac65a91

import Theorems.Thm_BanditAlgorithm_bandit_asymptotic_ucb_pull_count_failure_split
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_optimal_underestimation_count_bound
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_selected_overshoot_count_bound
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of Theorem 8.1,
Eq. (8.4), printed pp. 119--120 / PDF pp. 128--129.

The imported formal Eq. (8.4) splits pulls of the suboptimal arm after its
single initialization pull into optimal-index underestimation and selected
suboptimal-index overshoot counts.  The next two imported results are the two
expectation estimates displayed on the cited pages; the second uses the
already proved formal Lemma 8.2.
-/

theorem solution {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π)
    (n : ℕ) (i : Fin k) (ε : ℝ)
    (hgap : 0 < BanditAlgorithm.banditGap ν i) (hεpos : 0 < ε)
    (hεlt : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      1 + 5 / ε ^ 2 +
        2 / (BanditAlgorithm.banditGap ν i - ε) ^ 2 *
          (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
            Real.sqrt
              (Real.pi *
                Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) + 1) := by
  letI : Nonempty (Fin k) := ⟨i⟩
  obtain ⟨a, ha⟩ :=
    exists_eq_ciSup_of_finite
      (f := fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j)
  have ha' : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν := by
    simpa [BanditAlgorithm.banditOptimalMean] using ha
  have hsplit :=
    BanditAlgorithm.bandit_asymptotic_ucb_pull_count_failure_split
      hπ n a i ε ha'
  have hlow :=
    BanditAlgorithm.asymptotic_ucb_optimal_underestimation_count_bound
      (π := π) hν n a i ε ha' hεpos
  have hhigh :=
    BanditAlgorithm.asymptotic_ucb_selected_overshoot_count_bound
      (π := π) hν n a i ε ha' hgap hεpos hεlt
  linarith
