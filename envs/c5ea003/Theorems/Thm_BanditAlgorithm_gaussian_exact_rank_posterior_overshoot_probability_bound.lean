-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_posterior_overshoot_probability_bound
-- name    : BanditAlgorithm.gaussian_exact_rank_posterior_overshoot_probability_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:38:33.830274+00:00
-- url     : https://prove2.me/theorems/e3b58f2c-76c1-4d0b-bc09-6f69f92bf78b
-- title:
--   Gaussian posterior overshoot at one exact realized rank
-- statement:
--   Fix an optimal arm $i_0$, a suboptimal arm $i$ of gap $\Delta_i>0$, a separating offset $0<\varepsilon<\Delta_i$, a horizon $n\ge2$, and a positive exact realized rank $s$. On histories where arm $i$ has been pulled more than $s$ times, the probability that its rank-$s$ Gaussian posterior assigns more than $1/n$ mass above $\mu_* - \varepsilon$ is at most
--   $$
--   \begin{cases}
--   \exp\!\left[-\dfrac{s\left(\Delta_i-\varepsilon-\sqrt{2\log(n)/s}\right)^2}{2}\right],&\dfrac{2\log n}{(\Delta_i-\varepsilon)^2}<s,\\
--   1,&\text{otherwise.}
--   \end{cases}
--   $$
--   This is the arbitrary-threshold exact-rank form of the deviation estimate used in Exercise 36.6(b).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(b), printed p. 475 / PDF p. 484; Theorem 36.2 and Eq. (36.3), printed pp. 463–465 / PDF pp. 472–474; reward-stack construction in §4.6, printed p. 65 / PDF p. 74.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_exact_rank_posterior_overshoot_probability_bound :
    ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k),
      ∀ (i₀ : Fin k),
        BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ =
          BanditAlgorithm.banditOptimalMean (BanditAlgorithm.gaussianBandit μvec) →
      ∀ (i : Fin k), 0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i →
      ∀ ε : ℝ, 0 < ε →
        ε < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i →
      ∀ n : ℕ, 2 ≤ n →
      ∀ s : ℕ, 0 < s →
        (BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n).real
          {h : BanditAlgorithm.BanditHistory k n |
            s < BanditAlgorithm.armPullCount i h ∧
              1 / (n : ℝ) <
                BanditAlgorithm.gaussianTSTailProb i s
                  (BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ - ε) h} ≤
          if 2 * Real.log n /
                (BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i - ε) ^ 2 < (s : ℝ)
          then
            Real.exp
              (-((s : ℝ) *
                (BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i - ε -
                  Real.sqrt (2 * Real.log n / s))) ^ 2 /
                ((2 : ℝ) * (s : ℝ) * 1))
          else 1 := by sorry
