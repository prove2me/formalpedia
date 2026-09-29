-- Prove2me | Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_at_commit_time
-- name    : BanditAlgorithm.etc_arm_expected_pull_count_at_commit_time
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-07-21T02:22:42.893566+00:00
-- url     : https://prove2.me/theorems/9293b4ee-f6aa-45b7-9c99-9a9a110bcdcd
-- title:
--   ETC exploration occupation at commitment
-- statement:
--   Let $k>0$, let $m\ge0$, and run the round-robin exploration phase of Explore-Then-Commit for $mk$ rounds. Every arm $i$ is pulled exactly $m$ times, hence
--
--   $$\mathbb E[T_i(mk)]=m.$$
--
--   This is the exploration occupation identity used in Eq. (6.2). It is deterministic and remains valid for $m=0$; the reward laws need no tail assumption.
--
--   **Formalization Note** The expectation is the integral of the arm-pull count under the canonical bandit history measure.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 6.1, Theorem 6.1, printed p. 92 / PDF p. 101, Eq. (6.2).

import Definitions.Def_etcPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.etc_arm_expected_pull_count_at_commit_time
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    {m : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π) (i : Fin k) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π (m * k))
        (fun h : BanditAlgorithm.BanditHistory k (m * k) ↦
          (BanditAlgorithm.armPullCount i h : ℝ)) = m := by
  sorry
