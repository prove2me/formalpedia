-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_reciprocal_tail_laplace_envelope
-- name    : BanditAlgorithm.gaussian_reciprocal_tail_laplace_envelope
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:08:02.195721+00:00
-- url     : https://prove2.me/theorems/d280cfa0-523e-44d5-8f73-b51d95d32609
-- title:
--   Laplace-mixture envelope for reciprocal Gaussian tails
-- statement:
--   Let $Q(u)=\mathbb P\{Z>u\}$ for a standard Gaussian random variable $Z$. There is a universal constant $C>0$ such that, for every real $u$,
--
--   $$
--   \frac{1}{Q(u)}-1
--   \le C\int_0^\infty \lambda
--   \exp\!\left(\lambda u-\frac{\lambda^2}{2}\right)\,d\lambda.
--   $$
--
--   This inequality packages the reciprocal Gaussian-tail estimate as a nonnegative Laplace mixture. It is designed for reuse with exponential supermartingale or moment-generating-function bounds.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Gaussian-tail hint to Exercise 36.6(a), printed p. 475 / PDF p. 484. This is a purely analytic Laplace-mixture reformulation of the hinted Gaussian reciprocal-tail calculation.

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- A Laplace-mixture envelope for the reciprocal standard-Gaussian upper tail. -/
theorem gaussian_reciprocal_tail_laplace_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ENNReal.ofReal
          (1 / (gaussianReal 0 1).real (Set.Ioi u) - 1) ≤
        ENNReal.ofReal C *
          (∫⁻ l : ℝ in Set.Ioi 0,
            ENNReal.ofReal
              (l * Real.exp (l * u - l ^ 2 / 2))) := by
  sorry

end BanditAlgorithm
