-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line
-- name    : ConvexOptimization.leindler_supremal_integral_real_line
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T04:49:49.90607+00:00
-- url     : https://prove2.me/theorems/6661ebdc-b236-4e0a-a567-15b4dba47ac6
-- title:
--   Leindler's sharp one-dimensional supremal-envelope integral inequality
-- statement:
--   Let $0 < \lambda < 1$ and let $f,g : \mathbb{R} \to [0,+\infty]$ be measurable. For each $z\in\mathbb{R}$, define the sharp supremal envelope
--
--   $$
--   R_\lambda(f,g)(z)
--   = \sup\left\{
--   f(x)^{1-\lambda}g(y)^\lambda:
--   (1-\lambda)x+\lambda y=z
--   \right\}.
--   $$
--
--   Then
--
--   $$
--   \left(\int_{\mathbb{R}} f\right)^{1-\lambda}
--   \left(\int_{\mathbb{R}} g\right)^\lambda
--   \le \int_{\mathbb{R}}^- R_\lambda(f,g)(z)\,dz.
--   $$
--
--   This is the sharp one-dimensional supremal-envelope form of the Prékopa–Leindler inequality. Any function satisfying the usual Prékopa–Leindler pointwise hypothesis is a majorant of this envelope, so the result is reusable as the analytic core of majorant formulations.
--
--   **Formalization Note** The fiber supremum is represented by `sSup` in the complete lattice of extended nonnegative reals. The right side is a lower Lebesgue integral, so the formal statement does not require a separate measurability hypothesis for the uncountable supremal envelope and permits the value $+\infty$.
-- source:
--   András Prékopa, On logarithmic concave measures and functions, Acta Scientiarum Mathematicarum 34 (1973), 335–343, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, §2, p. 337, equation (2.2), specialized to k = 2 with weights 1−λ and λ and written in the extended-nonnegative lower-integral form.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_supremal_integral_real_line
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by sorry
