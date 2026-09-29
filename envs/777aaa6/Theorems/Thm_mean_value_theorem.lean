-- Prove2me | Theorems.Thm_mean_value_theorem
-- name    : mean_value_theorem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T13:16:26.462663+00:00
-- url     : https://prove2.me/theorems/564b289b-fd79-4b49-9085-46f7202d142a
-- statement:
--   Mean value theorem: For differentiable f on [a,b], there exists c with f'(c) = (f(b)-f(a))/(b-a). Proved. Fundamental in real analysis.
-- source:
--   https://en.wikipedia.org/wiki/Mean_value_theorem

import Mathlib

import Mathlib

theorem mean_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt f (deriv f x) x) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by
  sorry
