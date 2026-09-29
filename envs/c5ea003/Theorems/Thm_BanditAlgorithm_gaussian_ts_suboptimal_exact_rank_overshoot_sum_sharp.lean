-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:40:58.687303+00:00
-- url     : https://prove2.me/theorems/5e993a9a-1f5c-4e5c-84cd-63fc211a0a4c
-- title:
--   Sharp exact-rank Gaussian posterior-overshoot sum
-- statement:
--   Fix an optimal arm $i_0$, a suboptimal arm $i$ of gap $\Delta_i>0$, and $0<\varepsilon<\Delta_i$. Along the exact realized ranks of arm $i$, the expected number of posterior distributions that put more than $1/n$ mass above $\mu_* - \varepsilon$ satisfies
--   $$
--   \mathbb E\!\left[\sum_{s<T_i(n)}\mathbf 1\!\left\{G_{i,s}(\mu_* - \varepsilon)>\frac1n\right\}\right]
--   \le 1+\frac{2}{(\Delta_i-\varepsilon)^2}\left(\log n+\sqrt{\pi\log n}+1\right).
--   $$
--   The leading coefficient is therefore the sharp $2/(\Delta_i-\varepsilon)^2$ from Exercise 36.6(b).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(b), printed p. 475 / PDF p. 484, and Theorem 36.2, Eq. (36.3), printed pp. 463–465 / PDF pp. 472–474.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp :
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k),
        ∀ (i₀ : Fin k),
          BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ =
            BanditAlgorithm.banditOptimalMean (BanditAlgorithm.gaussianBandit μvec) →
        ∀ (i : Fin k), 0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i →
        ∀ ε : ℝ, 0 < ε →
          ε < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i →
        ∀ n : ℕ, 2 ≤ n →
          (∫⁻ h, ∑ s ∈ Finset.range (BanditAlgorithm.armPullCount i h),
              (if 1 / (n : ℝ) <
                  BanditAlgorithm.gaussianTSTailProb i s
                    (BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ - ε) h
                then (1 : ℝ≥0∞) else 0)
              ∂BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (1 + 2 / (BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i - ε) ^ 2 *
                (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by sorry
