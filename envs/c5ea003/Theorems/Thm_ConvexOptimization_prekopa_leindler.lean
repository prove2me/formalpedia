-- Prove2me | Theorems.Thm_ConvexOptimization_prekopa_leindler
-- name    : ConvexOptimization.prekopa_leindler
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:43:07.548022+00:00
-- url     : https://prove2.me/theorems/38f376c4-f6e0-43dc-a027-4ba049f313bd
-- title:
--   Prékopa–Leindler inequality
-- statement:
--   **The Prékopa–Leindler inequality** — the functional form of the Brunn–Minkowski inequality.
--
--   Let $0 < \lambda < 1$ and let $f, g, h : \mathbb{R}^n \to [0,+\infty]$ be measurable functions satisfying the pointwise hypothesis
--
--   $$f(x)^{1-\lambda}\, g(y)^{\lambda} \;\le\; h\bigl((1-\lambda)x + \lambda y\bigr) \qquad \text{for all } x, y \in \mathbb{R}^n .$$
--
--   Then the same multiplicative inequality holds for the integrals:
--
--   $$\Bigl(\int_{\mathbb{R}^n} f\Bigr)^{1-\lambda} \Bigl(\int_{\mathbb{R}^n} g\Bigr)^{\lambda} \;\le\; \int_{\mathbb{R}^n} h .$$
--
--   Applied to indicator functions of convex bodies $A$ and $B$, with $h$ the indicator of $(1-\lambda)A + \lambda B$, the hypothesis holds by convexity and the conclusion becomes $\operatorname{vol}(A)^{1-\lambda}\operatorname{vol}(B)^{\lambda} \le \operatorname{vol}((1-\lambda)A + \lambda B)$ — the multiplicative Brunn–Minkowski inequality. Remarkably, the hypothesis only constrains $h$ along the single interpolation point of each pair $(x,y)$, yet controls its whole integral, and there is no convexity or regularity assumption on any of the three functions.
--
--   This is the one genuinely analytic input of the mission: Prékopa's theorem on marginals follows from it by applying the inequality to the sections of a log-concave function.
--
--   **Formalization Note** The functions are `ℝ≥0∞`-valued and the integrals are lower Lebesgue integrals `∫⁻`, which removes every integrability side condition and makes the statement unconditional; the integrable real-valued form follows by truncation and monotone convergence. Source: Gardner, *The Brunn–Minkowski inequality*, BAMS 39 (2002), Theorem 4.2, verified verbatim; cited from B&V §3.5.2.
-- source:
--   Gardner 2002, The Brunn-Minkowski inequality, Bulletin of the American Mathematical Society 39(3), https://www.ams.org/journals/bull/2002-39-03/S0273-0979-02-00941-2/, Theorem 4.2 (the Prekopa-Leindler inequality), verified verbatim against the paper; cited from Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 105, §3.5.2. The lower-integral (ENNReal) form is implied by the integrable case via truncation and monotone convergence

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.prekopa_leindler {n : ℕ} (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by
  sorry
