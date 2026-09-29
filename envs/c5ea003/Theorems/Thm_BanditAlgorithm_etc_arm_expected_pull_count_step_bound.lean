-- Prove2me | Theorems.Thm_BanditAlgorithm_etc_arm_expected_pull_count_step_bound
-- name    : BanditAlgorithm.etc_arm_expected_pull_count_step_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-07-21T02:22:58.308943+00:00
-- url     : https://prove2.me/theorems/b39df0bb-af2b-4568-9301-8889f5d720e8
-- title:
--   ETC post-commit occupation recurrence
-- statement:
--   Let $k>0$, let $m\ge1$, and run Explore-Then-Commit on a 1-subgaussian $k$-armed bandit. For every arm $i$ and every post-exploration round $r\ge mk$,
--
--   $$\mathbb E[T_i(r+1)]\le \mathbb E[T_i(r)]+\exp\!\left(-rac{m\Delta_i^2}{4}ight).$$
--
--   The added term is the two-sample subgaussian probability that arm $i$ defeats an optimal arm at commitment, exactly the estimate in Eq. (6.3). The statement includes optimal arms ($\Delta_i=0$), where the bound remains valid.
--
--   **Formalization Note** Expectations are integrals under the canonical bandit history measures at horizons $r$ and $r+1$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 6.1, Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102, Eq. (6.3).

import Definitions.Def_etcPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.etc_arm_expected_pull_count_step_bound
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {m : ℕ} (hm : 1 ≤ m) {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π) (i : Fin k) :
    ∀ r : ℕ, m * k ≤ r →
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π (r + 1))
          (fun h : BanditAlgorithm.BanditHistory k (r + 1) ↦
            (BanditAlgorithm.armPullCount i h : ℝ)) ≤
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π r)
          (fun h : BanditAlgorithm.BanditHistory k r ↦
            (BanditAlgorithm.armPullCount i h : ℝ)) +
          Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  sorry
