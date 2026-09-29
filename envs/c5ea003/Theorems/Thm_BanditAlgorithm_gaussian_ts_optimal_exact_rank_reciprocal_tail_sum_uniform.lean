-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform
-- name    : BanditAlgorithm.gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T02:04:19.987817+00:00
-- url     : https://prove2.me/theorems/3d0dae6e-f34c-4f09-ad54-7d3e32298aab
-- title:
--   Uniform bound for the optimal-arm reciprocal posterior-tail sum
-- statement:
--   Let $i_0$ be an optimal arm in a unit-variance Gaussian bandit, and fix an offset $\varepsilon>0$. For every adaptive policy and every horizon $n$, consider the sum over the realized pull ranks $s<T_{i_0}(n)$ of the reciprocal posterior-tail penalty
--   $$
--   \frac{1}{\mathbb P(\theta_{i_0,s}>\mu_{i_0}-\varepsilon\mid\mathcal H)}-1.
--   $$
--   There is a universal constant $C>0$ such that the expectation of this sum is bounded uniformly in $n$ by
--   $$
--   \frac{2e^{\varepsilon^2/8}}{\varepsilon^2/8}
--   +\frac{2C}{\varepsilon^2}\,
--     \frac{e^{3\varepsilon^2/32}}{3\varepsilon^2/32}.
--   $$
--   In particular, the optimal-arm reciprocal-tail contribution is $O_{\varepsilon}(1)$ rather than logarithmic in the horizon. This is the finite-horizon form of the summability assertion used in Exercise 36.6(a).
--
--   **Formalization Note** The Lean integral includes exactly the ranks realized before time $n$; the displayed constant is an explicit finite envelope obtained from the exact-rank exponential estimate.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, Chapter 36, Exercise 36.6(a), printed p. 475 (PDF p. 484), together with the Gaussian posterior calculation in the solution outline.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit
import Mathlib.Analysis.SumIntegralExpDecay

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditAlgorithm.BanditPolicy k),
        ∀ (i₀ : Fin k),
          BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ =
            BanditAlgorithm.banditOptimalMean (BanditAlgorithm.gaussianBandit μvec) →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h, ∑ s ∈ Finset.range (BanditAlgorithm.armPullCount i₀ h),
              ENNReal.ofReal
                (1 / BanditAlgorithm.gaussianTSTailProb i₀ s
                  (BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i₀ - ε) h - 1)
              ∂BanditAlgorithm.banditMeasure (BanditAlgorithm.gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (2 * Real.exp (ε ^ 2 / 8) / (ε ^ 2 / 8) +
                (2 * C / ε ^ 2) *
                  (Real.exp (3 * ε ^ 2 / 32) / (3 * ε ^ 2 / 32))) := by sorry
