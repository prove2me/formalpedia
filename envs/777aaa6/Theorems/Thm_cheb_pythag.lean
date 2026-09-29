-- Prove2me | Theorems.Thm_cheb_pythag
-- name    : cheb_pythag
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T08:56:14.866114+00:00
-- url     : https://prove2.me/theorems/73c20473-396e-44d9-9205-6187b8ba0cf8
-- statement:
--   The Chebyshev 'Pythagorean' identity: (1-x^2) T'_d(x)^2 + d^2 T_d(x)^2 = d^2 for all real x. This is the algebraic form of sin^2(d theta) + cos^2(d theta) = 1 composed with x = cos theta, using T_d(cos theta) = cos(d theta), T'_d(cos theta) = d sin(d theta)/sin theta. Both sides are polynomials of degree 2d; the identity holds at infinitely many points (cos theta for theta in (0,pi)), so it holds as a polynomial identity, hence for all x. Can be proved by induction on d using the Chebyshev recurrence T_{d+2} = 2X T_{d+1} - T_d and T' derivative formula, or by evaluating on (cos theta) and lifting by Polynomial.eq_zero_of_infinite_isRoot. Also follows from Polynomial.Chebyshev.T_derivative_eq_U and the U_d identity.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem cheb_pythag (d : ℕ) :
    ∀ c : ℝ, (1 - c^2) * ((Polynomial.derivative (Polynomial.Chebyshev.T ℝ (d : ℤ))).eval c)^2 + (d : ℝ)^2 * ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval c)^2 = (d : ℝ)^2 := by sorry
