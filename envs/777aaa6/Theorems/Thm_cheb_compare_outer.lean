-- Prove2me | Theorems.Thm_cheb_compare_outer
-- name    : cheb_compare_outer
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T08:56:24.282087+00:00
-- url     : https://prove2.me/theorems/9ef8f1bb-1822-4240-9403-d326847b9f2e
-- statement:
--   Chebyshev comparison near the endpoints (the crux of Markov's last step). If p has degree < d and satisfies the Bernstein bound (1-x^2) p(x)^2 <= d^2 on [-1,1], then for c in [-1,1] with d^2(1-c^2) <= 1 (i.e., |c| >= sqrt(1-1/d^2) >= cos(pi/(2d))), we have |p(c)| <= |T'_d(c)|. Proof (root counting): At the d zeros t_j = cos((2j+1)pi/(2d)), j=0..d-1, of T_d, we have (1-t_j^2)T'_d(t_j)^2 = d^2 (by the Pythagorean identity), so |T'_d(t_j)| = d/sqrt(1-t_j^2), and the Bernstein bound gives |p(t_j)| <= d/sqrt(1-t_j^2) = |T'_d(t_j)|. T'_d alternates sign at the t_j: sign(T'_d(t_j)) = (-1)^j. So for mu in (0,1), R := T'_d - mu p has d sign alternations at t_0 > t_1 > ... > t_{d-1}, giving d-1 roots in (t_{d-1}, t_0). Since deg R <= d-1, these are all the roots, and R(c) has the same sign as R(t_0) > 0 for c >= t_0 (and sign (-1)^{d-1} for c <= t_{d-1}). Same for R' := T'_d + mu p. Taking mu -> 1 (or a direct no-limit argument: suppose |p(c)| > |T'_d(c)|, let mu := |T'_d(c)|/|p(c)| < 1, get an extra root for R, contradicting deg R <= d-1). Then |c| >= sqrt(1-1/d^2) >= cos(pi/(2d)) (Jordan's inequality sin t >= 2t/pi) guarantees c is outside (t_{d-1}, t_0). NOT in Mathlib.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem cheb_compare_outer (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (d : ℝ)^2 * (1 - c^2) ≤ 1 →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by sorry
