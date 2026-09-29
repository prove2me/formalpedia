-- Prove2me | solution 1 for BanditAlgorithm.etc_arm_expected_pull_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-20T20:23:00.926798+00:00
-- url     : https://prove2.me/submissions/cc6d5d41-2ad2-456f-b03f-8571c7b18ed2

import Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_recurrence
import Mathlib.Tactic

/-!
Reduction of the finite-horizon ETC occupation bound to the exact recurrence
used in Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), Theorem 6.1,
printed pp. 92--93, Eqs. (6.2)--(6.3).  The bridge below is purely formal:
iterate the source-backed one-step bound from the exact exploration count.
-/

open MeasureTheory ProbabilityTheory

theorem solution {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m * k ≤ n)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π) (i : Fin k) :
    ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
        ∂(BanditAlgorithm.banditMeasure ν π n) ≤
      m + (n - m * k : ℝ) *
        Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  obtain ⟨hbase, hstep⟩ :=
    BanditAlgorithm.etc_arm_expected_pull_count_recurrence hk hν hm hπ i
  let C : ℝ := Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4)
  have hmain : ∀ r : ℕ, m * k ≤ r →
      ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π r) ≤
        m + (r - m * k : ℝ) * C := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
        simpa [C] using le_of_eq hbase
    | succ r hr ihr =>
        calc
          (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
              ∂(BanditAlgorithm.banditMeasure ν π (r + 1))) ≤
              (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
                ∂(BanditAlgorithm.banditMeasure ν π r)) + C := by
                simpa [C] using hstep r hr
          _ ≤ (m + (r - m * k : ℝ) * C) + C := by linarith
          _ = m + (((r + 1 : ℕ) : ℝ) - (m : ℝ) * (k : ℝ)) * C := by
                push_cast
                ring
  simpa [C] using hmain n hmn
