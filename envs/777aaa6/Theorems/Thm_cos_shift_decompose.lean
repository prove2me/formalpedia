-- Prove2me | Theorems.Thm_cos_shift_decompose
-- name    : cos_shift_decompose
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T13:05:08.613995+00:00
-- url     : https://prove2.me/theorems/80df6cc8-4cd1-484c-801e-9fac0d2f02be
-- statement:
--   Odd-even decomposition of Q(cos(phi + theta)) as a trig polynomial in theta with polynomial coefficients in cos theta: there exist polynomials E (even part, deg <= deg Q) and P (odd part, deg <= deg Q - 1, or P = 0) such that Q(cos(phi + theta)) = E(cos theta) + P(cos theta) sin theta for all theta. And P(1) = -sin(phi) Q'(cos phi) (from d/dtheta at theta=0). Proof sketch: expand Q in the monomial basis Q = sum q_k X^k, and for each monomial cos(phi+theta)^k = (cos phi cos theta - sin phi sin theta)^k, binomial expansion and split by parity of the sin theta power (even powers: sin^2 theta = 1-cos^2 theta; odd powers: sin theta * (1-cos^2 theta)^j). E_k and P_k are polynomials with deg E_k <= k, deg P_k <= k-1. Sum up. Alternatively prove by structural induction: base cases C a (E=C a, P=0) and X (E = C(cos phi) X, P = C(-sin phi)); product Q1*Q2 gives E = E1 E2 + P1 P2 (1-X^2), P = E1 P2 + P1 E2 (with cos/sin product-to-sum). The additive case needs care on degrees (degree can drop when leading coeffs cancel), so the monomial-sum route or divX recursion is recommended. For P(1): differentiate the identity at theta=0, or track inductively (P(1) = -sin phi Q'(cos phi), with E(1) = Q(cos phi)). NOT in Mathlib.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

theorem cos_shift_decompose (Q : Polynomial ℝ) (φ : ℝ) :
    ∃ E P : Polynomial ℝ, E.natDegree ≤ Q.natDegree ∧ (P.natDegree + 1 ≤ Q.natDegree ∨ P = 0) ∧
      (∀ θ : ℝ, Q.eval (Real.cos (φ + θ)) = E.eval (Real.cos θ) + P.eval (Real.cos θ) * Real.sin θ) ∧
      P.eval 1 = -Real.sin φ * Q.derivative.eval (Real.cos φ) := by sorry
