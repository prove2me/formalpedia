-- Prove2me | Theorems.Thm_ns_markov_grid_lemma
-- name    : ns_markov_grid_lemma
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T03:10:38.949384+00:00
-- url     : https://prove2.me/theorems/923f7ec1-a794-44cb-95f6-8673dd03f42d
-- statement:
--   Markov / Coppersmith-Rivlin derivative bound on the integer grid (nonnegative form). For a polynomial Q of degree <= d with 0 <= Q(t) <= 1 on {0,...,b} (b >= 1) in the regime d^2 < b, we have |Q'(c)| <= d^2 / (b - d^2) for all c in [0,b]. This is the derivative bound in the Nisan-Szegedy Cor. 9 argument. Proof sketch: let M, m be the max/min of Q on [0,b] (exists by compactness). Classical Markov on [0,b]: |Q'| <= d^2(M-m)/b. Nearest-integer-point bound: M <= 1 + (d^2(M-m)/b)/2, m >= -(d^2(M-m)/b)/2, so M - m <= 1 + d^2(M-m)/b. Algebra: M - m <= b/(b-d^2), hence |Q'| <= d^2/(b-d^2). Requires: classical Markov brothers inequality on intervals (NOT in Mathlib), MVT for the nearest-integer bound, compactness for the extremum. Estimated 300-500 lines.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem ns_markov_grid_lemma
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ))
    (h_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1)
    (h_d2b : (d : ℝ)^2 < (b : ℝ)) :
    ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ (d : ℝ)^2 / ((b : ℝ) - (d : ℝ)^2) := by sorry
