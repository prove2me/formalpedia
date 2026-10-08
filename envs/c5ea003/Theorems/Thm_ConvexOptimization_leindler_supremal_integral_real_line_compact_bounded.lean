-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_compact_bounded
-- name    : ConvexOptimization.leindler_supremal_integral_real_line_compact_bounded
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T05:11:36.068054+00:00
-- url     : https://prove2.me/theorems/8115aecd-9b25-4409-b3d5-c254f9909040
-- title:
--   Leindler's sharp real-line inequality for bounded compactly supported inputs
-- statement:
--   Let $0 < \lambda < 1$. Let $f,g : \mathbb{R} \to [0,+\infty]$ be measurable functions with compact support, and suppose they admit finite bounds $B_f,B_g < +\infty$ such that $f(x)\le B_f$ and $g(x)\le B_g$ for every $x$. Define
--
--   $$
--   R_\lambda(f,g)(z)=\sup\left\{f(x)^{1-\lambda}g(y)^\lambda:(1-\lambda)x+\lambda y=z\right\}.
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
--   This finite, compactly supported form isolates the classical analytic core of the one-dimensional Prékopa–Leindler inequality and is suitable for a level-set and one-dimensional Brunn–Minkowski proof.
--
--   **Formalization Note** The bounds are nonnegative real numbers coerced into the extended nonnegative reals. The supremal envelope is integrated using the lower Lebesgue integral, so no separate Borel-measurability hypothesis on that envelope is imposed.
-- source:
--   András Prékopa, On logarithmic concave measures and functions, Acta Scientiarum Mathematicarum 34 (1973), 335–343, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, §2, p. 337, equation (2.2), specialized to k = 2 with weights 1−λ and λ, functions f₁=f^(1−λ), f₂=g^λ, and bounded compactly supported inputs.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_supremal_integral_real_line_compact_bounded
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (Bf Bg : NNReal)
    (hfB : ∀ x, f x ≤ (Bf : ENNReal))
    (hgB : ∀ x, g x ≤ (Bg : ENNReal)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  sorry
