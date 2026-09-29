-- Prove2me | Theorems.Thm_ns_lemma2_nonneg
-- name    : ns_lemma2_nonneg
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T02:57:45.661876+00:00
-- url     : https://prove2.me/theorems/8571c98f-e600-406d-9e35-cfda70d7e742
-- statement:
--   Nisan-Szegedy 1994 Lemma 2 (nonnegative form). For a univariate real polynomial Q of degree <= d with Q(0) = 0, Q(1) = 1, and 0 <= Q(t) <= 1 on the integer grid {0,...,b} (b >= 1), we have b <= 2 d^2. This is the form with b_1 = 0, b_2 = 1 which gives exactly constant 2 via the Markov/Cor-9 argument; the |Q| <= 1 form (markov_brothers_integer_grid_v2) gives only 3 d^2 via the same route. Proof needs classical Markov brothers inequality on intervals + MVT + the nearest-grid-point bound.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

theorem ns_lemma2_nonneg
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1)
    (h_lo : ∀ t : ℕ, t ≤ b → 0 ≤ Q.eval (t : ℝ))
    (h_hi : ∀ t : ℕ, t ≤ b → Q.eval (t : ℝ) ≤ 1) :
    b ≤ 2 * d^2 := by sorry
