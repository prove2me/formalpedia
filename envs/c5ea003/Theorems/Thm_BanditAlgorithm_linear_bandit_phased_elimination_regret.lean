-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_phased_elimination_regret
-- name    : BanditAlgorithm.linear_bandit_phased_elimination_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:39:56.37631+00:00
-- url     : https://prove2.me/theorems/c6da0f76-077b-4ebf-805a-0eac3915c1e0
-- statement:
--   (Phased elimination with G-optimal design — Theorem 22.1) There is a universal constant $C>0$ such that for every fixed action set of $k$ arms in $\mathbb{R}^d$, horizon $n \ge 2$ and $\delta \in (0,1)$ there is a policy $\pi$ (Algorithm 12: phased elimination with G-optimal exploration) such that on every linear bandit instance with gaps $\Delta_a \le 1$: with probability at least $1-\delta$, the random regret satisfies
--
--   $$\sum_a T_a(n)\Delta_a \le C\sqrt{nd\log(k\log(n)/\delta)};$$
--
--   and if $\delta = 1/n$, the expected regret satisfies
--
--   $$R_n \le C\sqrt{nd\log(kn)}.$$
-- source:
--   L&S Theorem 22.1, p.273

import Definitions.Def_StochasticLinearBandit
import Definitions.Def_banditRegret


open Matrix MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.linear_bandit_phased_elimination_regret :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k d n : ℕ), 0 < k → 0 < d → 2 ≤ n →
        ∀ (arms : Fin k → Fin d → ℝ) (δ : ℝ), δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ π : BanditPolicy k,
            ∀ (θstar : Fin d → ℝ) (ν : StochasticBandit k),
              IsLinearBandit arms θstar ν →
              (∀ i, banditGap ν i ≤ 1) →
              1 - δ ≤ (banditMeasure ν π n).real
                  {h | ∑ i, (armPullCount i h : ℝ) * banditGap ν i ≤
                    C * Real.sqrt (n * d * Real.log (k * Real.log n / δ))} ∧
              (δ = 1 / n →
                banditRegret ν π n ≤
                  C * Real.sqrt (n * d * Real.log (k * n))) := by
  sorry
