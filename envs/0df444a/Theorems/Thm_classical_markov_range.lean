-- Prove2me | Theorems.Thm_classical_markov_range
-- name    : classical_markov_range
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T03:55:23.995829+00:00
-- url     : https://prove2.me/theorems/d3b7ae9a-75c9-4f38-853c-e3c96f3f227a
-- statement:
--   Classical Markov brothers inequality (A. Markov 1889) on a general interval [a,b], in range form: if a real polynomial Q of degree <= d satisfies m <= Q(x) <= M for all x in [a,b], then |Q'(c)| <= d^2 * (M - m) / (b - a) for all c in [a,b]. Equivalent to the |Q| <= 1 on [-1,1] => |Q'| <= d^2 form (by affine scaling). Equality for scaled Chebyshev T_d. NOT in Mathlib. Proof paths: (1) sign-change / root-counting argument with Chebyshev oscillation, (2) Bernstein inequality + Schur, (3) Chebyshev expansion with Chebyshev coefficients bounded by 1. Estimated 1000-2000 lines, may need Chebyshev polynomial extremal theory added to Mathlib.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem classical_markov_range
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (m M : ℝ)
    (hm : ∀ x : ℝ, a ≤ x → x ≤ b → m ≤ Q.eval x)
    (hM : ∀ x : ℝ, a ≤ x → x ≤ b → Q.eval x ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b → |Q.derivative.eval c| ≤ (d : ℝ)^2 * (M - m) / (b - a) := by sorry
