-- Prove2me | Theorems.Thm_mme_finite_variance_below_half_mean_card
-- name    : mme_finite_variance_below_half_mean_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:29:30.356369+00:00
-- url     : https://prove2.me/theorems/425ad964-2cef-4545-a88d-268cc8eebd5b
-- title:
--   Finite variance bounds the number of samples below half the mean
-- statement:
--   Let $f$ be nonnegative on a finite parameter set $U$, let $\mu\ge0$, and suppose\n\n$$\n\sum_{\omega\in U}(f(\omega)-\mu)^2\le V.\n$$\n\nThen the number of parameters at or below half the reference mean satisfies\n\n$$\n\mu^2\,\bigl|\{\omega\in U:2f(\omega)\le\mu\}\bigr|\le4V.\n$$\n\nThis cross-multiplied lower-tail Chebyshev estimate is useful when a second moment is close to the square of the mean and one needs almost all, rather than merely a constant fraction, of the finite parameters to be good.
-- source:
--   Finite one-sided Chebyshev inequality in cross-multiplied form

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_finite_variance_below_half_mean_card
    {Ω : Type} [DecidableEq Ω]
    (U : Finset Ω) (f : Ω → ℝ) (μ V : ℝ)
    (hf : ∀ ω ∈ U, 0 ≤ f ω)
    (hμ : 0 ≤ μ)
    (hvar : ∑ ω ∈ U, (f ω - μ) ^ 2 ≤ V) :
    μ ^ 2 * ((U.filter (fun ω => 2 * f ω ≤ μ)).card : ℝ) ≤ 4 * V := by
  sorry
