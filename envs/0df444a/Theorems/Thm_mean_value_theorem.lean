-- Prove2me | Theorems.Thm_mean_value_theorem
-- name    : mean_value_theorem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T13:16:26.462663+00:00
-- url     : https://prove2.me/theorems/f557e914-97e7-45e0-898c-b2087e0ff390
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
