-- Prove2me | Theorems.Thm_ConvexOptimization_prekopa_leindler_dimension_step
-- name    : ConvexOptimization.prekopa_leindler_dimension_step
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-14T16:22:51.407063+00:00
-- url     : https://prove2.me/theorems/30236020-07ee-4c03-b02d-2c50748e786f
-- title:
--   Prékopa–Leindler dimension-induction step
-- statement:
--   For $d \ge 0$, let $\mathrm{PL}_d$ denote the following assertion: for every $0<\lambda<1$ and every measurable $f,g,h : \mathbb{R}^d \to [0,+\infty]$ satisfying
--
--   $$
--   f(x)^{1-\lambda}g(y)^{\lambda} \le h((1-\lambda)x+\lambda y)
--   $$
--
--   for all $x,y$, one has
--
--   $$
--   \left(\int f\right)^{1-\lambda}\left(\int g\right)^{\lambda} \le \int h.
--   $$
--
--   If $\mathrm{PL}_1$ and $\mathrm{PL}_n$ hold, then $\mathrm{PL}_{n+1}$ holds.
-- source:
--   Richard J. Gardner, The Brunn-Minkowski Inequality: A Survey with Proofs, https://faculty.gardner.wwu.edu/gorizia12.pdf, induction in Theorem 4.2 (pp. 8-9); András Prékopa, Logarithmic concave measures with applications to stochastic programming, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, Theorem 3.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.prekopa_leindler_dimension_step {n : ℕ}
    (h_one :
      ∀ (l : ℝ) (_hl0 : 0 < l) (_hl1 : l < 1)
        (f g h : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞),
        Measurable f → Measurable g → Measurable h →
        (∀ x y : EuclideanSpace ℝ (Fin 1),
          f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x)
    (h_n :
      ∀ (l : ℝ) (_hl0 : 0 < l) (_hl1 : l < 1)
        (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
        Measurable f → Measurable g → Measurable h →
        (∀ x y : EuclideanSpace ℝ (Fin n),
          f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin (n + 1)),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by sorry
