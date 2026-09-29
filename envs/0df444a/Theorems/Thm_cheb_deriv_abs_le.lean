-- Prove2me | Theorems.Thm_cheb_deriv_abs_le
-- name    : cheb_deriv_abs_le
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T08:56:19.443262+00:00
-- url     : https://prove2.me/theorems/b3bc2c38-1016-447f-9911-c520fbc8b6b1
-- statement:
--   The Chebyshev derivative bound: |T'_d(c)| <= d^2 for all c in [-1,1]. Equality at c = +-1 where T'_d(+-1) = +-d^2 or = d^2. Proof: T'_d(cos theta) = d sin(d theta)/sin theta = d U_{d-1}(cos theta), and |sin(d theta)| <= d |sin theta| (proved by induction on d: |sin((d+1)theta)| = |sin(d theta)cos theta + cos(d theta)sin theta| <= |sin(d theta)| + |sin theta| <= (d+1)|sin theta|), hence |T'_d(cos theta)| <= d^2. At theta in {0, pi}, by continuity (or T'_d(+-1) computation). Also follows from T'_d = d * U_{d-1} and |U_{d-1}(x)| <= d on [-1,1].
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem cheb_deriv_abs_le (d : ℕ) :
    ∀ c : ℝ, -1 ≤ c → c ≤ 1 → |(Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c| ≤ (d : ℝ)^2 := by sorry
