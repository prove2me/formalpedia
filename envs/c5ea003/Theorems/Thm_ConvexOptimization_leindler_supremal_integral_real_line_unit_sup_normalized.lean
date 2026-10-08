-- Prove2me | Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line_unit_sup_normalized
-- name    : ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T06:09:36.023761+00:00
-- url     : https://prove2.me/theorems/f7739226-75b7-4e92-b419-adfd20f72be5
-- title:
--   Supremum-normalized one-dimensional Leindler inequality
-- statement:
--   Let $0 < \lambda < 1$, and let $f,g:\mathbb R\to[0,\infty]$ be measurable, compactly supported functions bounded above by one. Assume moreover that their pointwise suprema are both exactly one. For each $z\in\mathbb R$, define the supremal envelope
--   $$
--   R_\lambda(z)=\sup\{f(x)^{1-\lambda}g(y)^\lambda:(1-\lambda)x+\lambda y=z\}.
--   $$
--   Then
--   $$
--   \left(\int_{\mathbb R} f\right)^{1-\lambda}\left(\int_{\mathbb R} g\right)^\lambda \le \int_{\mathbb R}R_\lambda(z)\,dz.
--   $$
--   This is the supremum-normalized analytic core of the first proof of the one-dimensional Prékopa–Leindler inequality. It is reusable as the layer-cake core after independently rescaling two bounded inputs by their pointwise suprema.
--   **Formalization Note** Functions and lower Lebesgue integrals take values in the extended nonnegative reals, and the pointwise supremum is written as `sSup (Set.range f)`.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1, first proof, PDF pp. 6-7, especially the supremum-one normalization and level-set argument; together with the layer-cake formula (5) and Theorem 2.1, equation (2).

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  sorry
