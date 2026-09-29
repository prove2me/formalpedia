-- Prove2me | Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_recurrence
-- name    : BanditAlgorithm.etc_arm_expected_pull_count_recurrence
-- status  : Proved
-- author  : @ann
-- created : 2026-07-20T20:21:44.876631+00:00
-- url     : https://prove2.me/theorems/d9642e69-11ac-4d09-9257-90dbafb930dc
-- title:
--   ETC occupation-count recurrence
-- statement:
--   Let ν be a k-armed bandit with k > 0 whose reward laws are 1-subgaussian, and let π be the Explore-Then-Commit policy with m ≥ 1 exploration pulls per arm. For arm i, write T_i(r) for its number of pulls after r rounds and Δ_i for its suboptimality gap. Then
--
--   $$
--   \mathbb E[T_i(mk)] = m,
--   \qquad
--   \mathbb E[T_i(r+1)] \le \mathbb E[T_i(r)] + \exp\!\left(-\frac{m\Delta_i^2}{4}\right)
--   \quad\text{for every }r\ge mk.
--   $$
--
--   This recurrence packages the exact exploration occupation count and the per-round post-commit error control used in the ETC regret analysis. It is reusable for finite-horizon occupation and regret bounds, and it remains valid for an optimal arm where Δ_i = 0.
--
--   Source anchor: Lattimore--Szepesvári, Section 6.1, Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102, Eqs. (6.2)--(6.3).
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (CUP 2020), Section 6.1, Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102, Eqs. (6.2)--(6.3).

import Definitions.Def_etcPolicy

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), Section 6.1,
Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102, Eqs. (6.2)--(6.3).

This is the source's occupation-count recurrence: exploration contributes
exactly `m` pulls of every arm, and every subsequent ETC round contributes at
most the two-sample subgaussian commit-error probability.
-/

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.etc_arm_expected_pull_count_recurrence
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
  sorry
