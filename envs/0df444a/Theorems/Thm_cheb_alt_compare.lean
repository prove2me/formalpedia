-- Prove2me | Theorems.Thm_cheb_alt_compare
-- name    : cheb_alt_compare
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T11:57:12.907372+00:00
-- url     : https://prove2.me/theorems/c8dad21c-5c70-48b2-a8cd-709ba094077d
-- statement:
--   The Chebyshev root-counting comparison (core of Markov's last step). If p has degree < d and satisfies the Bernstein bound (1-x^2) p(x)^2 <= d^2 on [-1,1], then for c in [-1,1] with |c| >= cos(pi/(2d)) (i.e., c outside or at the boundary of the open interval spanned by the d zeros of T_d), |p(c)| <= |T'_d(c)|. Proof: The d zeros of T_d are t_j = cos((2j+1)pi/(2d)), j=0..d-1, strictly decreasing, with t_0 = cos(pi/(2d)), t_{d-1} = -cos(pi/(2d)). At each t_j: T_d(t_j) = 0 (cos of odd multiple of pi/2), (1-t_j^2) T'_d(t_j)^2 = d^2 (by the Pythagorean identity, since T_d(t_j)=0), and sign(T'_d(t_j)) = (-1)^j (T'_d(cos theta) = d sin(d theta)/sin theta, and sin((2j+1)pi/2) = (-1)^j). The Bernstein bound gives |p(t_j)| <= d/sqrt(1-t_j^2) = |T'_d(t_j)|. Root-counting argument: suppose |p(c)| > |T'_d(c)| for c >= t_0. WLOG p(c) > 0 (else negate p). First show T'_d(c) > 0 (T'_d alternates at t_j, has d-1 roots in (t_{d-1}, t_0), deg <= d-1, no roots outside, positive at t_0 so positive for c >= t_0). Let mu := T'_d(c)/p(c) in (0,1). R := T'_d - mu p. R(c) = 0, R alternates in sign strictly at the d points t_j (since |mu p(t_j)| < |T'_d(t_j)|), so R has d-1 roots in (t_{d-1}, t_0) plus one at c, d total distinct roots. deg R <= d-1. R != 0 (R(t_0) > 0). Contradiction. Symmetric for c <= t_{d-1}. NOT in Mathlib. Uses Polynomial.card_roots', IVT for polynomials, Chebyshev T_real_cos and T_derivative_eq_U.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

theorem cheb_alt_compare (p : Polynomial ℝ) {d : ℕ} (hd1 : 1 ≤ d) (hd : p.natDegree < d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → (1 - x^2) * (p.eval x)^2 ≤ (d : ℝ)^2) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → Real.cos (Real.pi / (2 * (d : ℝ))) ≤ |c| →
      |p.eval c| ≤ |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| := by sorry
