-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_eventual_lower
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_lower
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:33:44.342032+00:00
-- url     : https://prove2.me/theorems/8da4c00f-3af2-4332-a514-5d09e7afbf86
-- title:
--   Gaussian TS: eventual lower half of the armwise asymptotic
-- statement:
--   Fix a suboptimal arm $i$ of gap $\Delta_i>0$ under Gaussian Thompson sampling. For every real number $a<2/\Delta_i^2$, all sufficiently large horizons satisfy
--   $$
--   a<\frac{\mathbb E[T_i(n)]}{\log n}.
--   $$
--   Equivalently, the lower asymptotic envelope of the normalized expected pull count is at least $2/\Delta_i^2$. This is the armwise change-of-measure (Lai--Robbins) half of the proof of Theorem 36.3.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 36.3 and Exercise 36.6(c), printed pp. 465 and 475 / PDF pp. 474 and 484; the lower half uses the fundamental asymptotic change-of-measure lower bound of Chapter 16.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_lower
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i) :
    ∀ a : ℝ, a < 2 / BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i ^ 2 →
      ∀ᶠ n : ℕ in Filter.atTop,
        a <
          (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
            ∂BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n) /
              Real.log n := by sorry
