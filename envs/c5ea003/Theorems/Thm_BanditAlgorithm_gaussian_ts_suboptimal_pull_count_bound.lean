-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_bound
-- name    : BanditAlgorithm.gaussian_ts_suboptimal_pull_count_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:28:51.662283+00:00
-- url     : https://prove2.me/theorems/a6474cf7-4548-464a-a98e-ceb25fde3a07
-- title:
--   Finite-time pull count bound for Gaussian Thompson sampling
-- statement:
--   There is a universal constant $C>0$ such that Gaussian Thompson sampling satisfies the following finite-time pull-count estimate. For every unit-variance Gaussian bandit, every suboptimal arm $i$ with gap $\Delta_i>0$, and every horizon $n\ge2$,
--
--   $$
--   \mathbb E[T_i(n)]
--   \le C\left(1+\frac{\log n}{\Delta_i^2}\right).
--   $$
--
--   This is the gap-dependent probabilistic estimate obtained by applying the pull-count decomposition of Theorem 36.2 to Gaussian posterior tails. It implies both the instance-dependent logarithmic regret bound and, after a small-gap/large-gap split, the distribution-free $O(\sqrt{kn\log n})$ bound.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.3 and Exercise 36.6, printed pp. 465 and 477; derived from Theorem 36.2, Eq. (36.3), printed p.463.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_ts_suboptimal_pull_count_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        IsGaussianTSPolicy π →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
          ∀ n : ℕ, 2 ≤ n →
            ∫ h, (armPullCount i h : ℝ)
                ∂banditMeasure (gaussianBandit μvec) π n ≤
              C * (1 + Real.log n /
                banditGap (gaussianBandit μvec) i ^ 2) := by
  sorry
