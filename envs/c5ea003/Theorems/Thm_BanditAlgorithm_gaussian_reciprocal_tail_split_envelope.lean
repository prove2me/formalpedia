-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_reciprocal_tail_split_envelope
-- name    : BanditAlgorithm.gaussian_reciprocal_tail_split_envelope
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:43:20.485769+00:00
-- url     : https://prove2.me/theorems/f9046885-9d04-465b-acb4-7473e3c36ef3
-- title:
--   Split envelope for reciprocal Gaussian tails
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $Q(u)=\mathbb P\{Z>u\}$ for $Z\sim\mathcal N(0,1)$, and fix $a>0$. If $u\le-a/2$, then
--   $$
--   \frac1{Q(u)}-1\le2e^{-a^2/8}.
--   $$
--   For the complementary region, the reciprocal tail is bounded by the Laplace mixture
--   $$
--   \frac1{Q(u)}-1\le C\int_0^\infty \ell\,e^{\ell u-\ell^2/2}\,d\ell.
--   $$
--   This split keeps the exponentially small contribution on the typical side while retaining a nonnegative exponential-mixture envelope on the rare side.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Gaussian Mills-ratio hint for Exercise 36.6(a), printed p. 475 / PDF p. 484; Abramowitz and Stegun (1964), §7.1.13.

import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.gaussian_reciprocal_tail_split_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ u : ℝ,
      ENNReal.ofReal
          (1 / (gaussianReal 0 1).real (Set.Ioi u) - 1) ≤
        if u ≤ -a / 2 then
          ENNReal.ofReal (2 * Real.exp (-a ^ 2 / 8))
        else
          ENNReal.ofReal C *
            (∫⁻ l : ℝ in Set.Ioi 0,
              ENNReal.ofReal
                (l * Real.exp (l * u - l ^ 2 / 2))) := by sorry
