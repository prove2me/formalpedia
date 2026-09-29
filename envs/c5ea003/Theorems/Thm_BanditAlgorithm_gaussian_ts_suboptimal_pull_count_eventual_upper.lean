-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_eventual_upper
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_upper
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:34:03.733634+00:00
-- url     : https://prove2.me/theorems/8544409a-baf6-4f39-95aa-d6b02eae5a6a
-- title:
--   Gaussian TS: eventual upper half of the armwise asymptotic
-- statement:
--   Fix a suboptimal arm $i$ of gap $\Delta_i>0$ under Gaussian Thompson sampling. For every real number $b>2/\Delta_i^2$, all sufficiently large horizons satisfy
--   $$
--   \frac{\mathbb E[T_i(n)]}{\log n}<b.
--   $$
--   Equivalently, the upper asymptotic envelope of the normalized expected pull count is at most $2/\Delta_i^2$. This is the posterior-tail calculation in Exercise 36.6(a,b), combined with the pull-count decomposition (36.3).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 36.2, Eq. (36.3), printed pp. 463–465 / PDF pp. 472–474, and Exercise 36.6(a,b), printed p. 475 / PDF p. 484.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_upper
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i) :
    ∀ b : ℝ, 2 / BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i ^ 2 < b →
      ∀ᶠ n : ℕ in Filter.atTop,
        (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n) /
            Real.log n < b := by sorry
