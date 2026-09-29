-- Prove2me | Theorems.Thm_bernstein_unit
-- name    : bernstein_unit
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T07:55:50.492803+00:00
-- url     : https://prove2.me/theorems/5dddcab2-253d-40de-b185-acf4a0e98fa9
-- statement:
--   Bernstein inequality for algebraic polynomials (S. Bernstein 1912, building on A. Markov 1889), squared form to avoid sqrt: if |Q(x)| <= 1 on [-1,1] and deg Q <= d, then (1-c^2) Q'(c)^2 <= d^2 for all c in [-1,1]. Equivalently |Q'(c)| sqrt(1-c^2) <= d. At c = +-1 the statement is 0 <= d^2, trivial. Equality for Chebyshev T_d at certain interior points. NOT in Mathlib. Proof: pass to the trigonometric polynomial f(theta) := Q(cos theta), which has degree <= d and |f| <= 1. Then f'(theta) = -Q'(cos theta) sin theta, and trigonometric Bernstein gives |f'| <= d. Trigonometric Bernstein is proved by a root-counting argument (Szego): compare f to the extremal cos(d(theta - phi)) near a point where |f'| is maximal. Alternatively: Chebyshev comparison / Schaake-van der Corput identity (1-x^2)T'_d(x)^2 + d^2 T_d(x)^2 = d^2.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem bernstein_unit (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |Q.eval x| ≤ 1) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → (1 - c^2) * (Q.derivative.eval c)^2 ≤ (d : ℝ)^2 := by sorry
