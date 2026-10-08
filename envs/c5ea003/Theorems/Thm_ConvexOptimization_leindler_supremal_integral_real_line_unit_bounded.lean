-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_bounded
-- name    : ConvexOptimization.leindler_supremal_integral_real_line_unit_bounded
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T05:46:18.62743+00:00
-- url     : https://prove2.me/theorems/8782d103-96e3-47be-ad26-c37c4c077a4f
-- title:
--   Unit-bounded one-dimensional Leindler supremal inequality
-- statement:
--   Let 0 < λ < 1, and let f and g be measurable functions from ℝ to the extended nonnegative reals. Assume that both functions have compact support and satisfy f(x) ≤ 1 and g(x) ≤ 1 for every x. For z ∈ ℝ define R_λ(z) to be the supremum of f(x)^(1-λ) g(y)^λ over all x,y with (1-λ)x+λy=z. Then
--
--
--   (∫_ℝ f)^{1-λ}(∫_ℝ g)^λ ≤ ∫_ℝ R_λ(z) dz.
--
--
--   This is the unit-bounded compact-support subcase of the one-dimensional Prékopa–Leindler inequality. It isolates the analytic core needed to recover arbitrary finite pointwise bounds by scaling.
--
--   **Formalization Note** The functions and lower Lebesgue integrals take values in ℝ≥0∞, and the envelope is represented by the supremum of its attainable values at each z.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1, first proof, PDF pp. 6–7 (unit-bounded compact-support specialization); A. Prékopa, On logarithmic concave measures and functions, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, Eq. (2.2), p. 337.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_supremal_integral_real_line_unit_bounded
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  sorry
