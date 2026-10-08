-- Prove2me | Theorems.Thm_ConvexOptimization_weighted_unit_grid_sum_le_supremal_envelope_lintegral
-- name    : ConvexOptimization.weighted_unit_grid_sum_le_supremal_envelope_lintegral
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T07:50:45.063169+00:00
-- url     : https://prove2.me/theorems/4fc27193-0aa8-40c0-bd0a-8973a646827c
-- title:
--   Finite uniform-grid estimate for the weighted supremal envelope
-- statement:
--   Let $0<\lambda<1$, let $N\ge 1$, and let $f,g:\mathbb R\to[0,\infty]$ be measurable, compactly supported functions bounded above by one, each with pointwise supremum one. Put $\delta_N=1/(N+1)$ and
--
--   $$
--   A_{i,N}=\{x:(i+1)\delta_N\le f(x)\},\qquad
--   B_{i,N}=\{y:(i+1)\delta_N\le g(y)\}
--   $$
--
--   for $0\le i<N$. Define the weighted supremal envelope
--
--   $$
--   H(z)=\sup\{f(x)^{1-\lambda}g(y)^\lambda:(1-\lambda)x+\lambda y=z\}.
--   $$
--
--   Then
--
--   $$
--   \delta_N\sum_{i=0}^{N-1}\big((1-\lambda)|A_{i,N}|+\lambda|B_{i,N}|\big)
--   \le \int_{\mathbb R}H(z)\,dz.
--   $$
--
--   This finite-level estimate is the geometric core of the layer-cake proof of the normalized one-dimensional Prékopa--Leindler inequality. It is reusable independently of the limiting passage from uniform level grids to integrals.
--
--   **Formalization Note** Measures, coefficients, the supremal envelope, and lower integrals are extended nonnegative real numbers.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, PDF p. 5, equations (4)-(5), and Theorem 4.1 first proof, PDF pp. 6-7; the finite uniform sums are the lower level-set sums for equation (5).

import Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory Set

theorem ConvexOptimization.weighted_unit_grid_sum_le_supremal_envelope_lintegral
    (N : ℕ) (hN : 0 < N)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i : Fin N,
          (ENNReal.ofReal (1 - l) * volume
              {x : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ f x} +
            ENNReal.ofReal l * volume
              {y : ℝ | (((i.val + 1 : ℕ) : ℝ≥0∞) / (N + 1 : ℕ)) ≤ g y}) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  sorry
