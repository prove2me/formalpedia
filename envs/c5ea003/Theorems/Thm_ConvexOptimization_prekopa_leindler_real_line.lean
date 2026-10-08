-- Prove2me | Theorems.Thm_ConvexOptimization_prekopa_leindler_real_line
-- name    : ConvexOptimization.prekopa_leindler_real_line
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T02:47:11.677352+00:00
-- url     : https://prove2.me/theorems/07491312-285c-45f2-ab3b-f2158c8d8ae1
-- title:
--   One-dimensional Prékopa–Leindler inequality on ℝ (lower-integral form)
-- statement:
--   Let $0 < \lambda < 1$, and let $f,g,h : \mathbb{R} \to [0,+\infty]$ be measurable. Assume that for every $x,y \in \mathbb{R}$,
--
--   $$
--   f(x)^{1-\lambda}g(y)^{\lambda} \le h((1-\lambda)x+\lambda y).
--   $$
--
--   Then their lower Lebesgue integrals satisfy
--
--   $$
--   \left(\int_{\mathbb{R}} f\right)^{1-\lambda}
--   \left(\int_{\mathbb{R}} g\right)^{\lambda}
--   \le \int_{\mathbb{R}} h.
--   $$
--
--   This is the canonical real-coordinate form of the one-dimensional Prékopa–Leindler inequality. It isolates the analytic core from any particular finite-dimensional Euclidean-space representation, making it reusable under measure-preserving linear coordinate changes.
--
--   **Formalization Note** Function values and integrals lie in the extended nonnegative reals, so $+\infty$ is permitted. Scalar multiplication on $\mathbb{R}$ expresses the affine interpolation in the same form used by general real modules.
-- source:
--   Richard J. Gardner, The Brunn-Minkowski Inequality: A Survey with Proofs, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 4.1 (pp. 6–8); András Prékopa, On logarithmic concave measures and functions, Acta Sci. Math. 34 (1973), 335–343, https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf, §2, equations (2.1)–(2.2), for the arbitrary-weight extended-integral formulation; András Prékopa, Logarithmic concave measures with application to stochastic programming, Acta Sci. Math. 32 (1971), 301–316, https://acta.bibl.u-szeged.hu/14319/1/math_032_fasc_003_004_301-316.pdf, Theorem 1 (pp. 303–308), for the measurable half-weight case with infinite integrals explicitly permitted.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.prekopa_leindler_real_line
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : ℝ,
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by sorry
