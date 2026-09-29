-- Prove2me | Theorems.Thm_LinearOptimization_farkas_inequality_form
-- name    : LinearOptimization.farkas_inequality_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T18:43:27.967263+00:00
-- url     : https://prove2.me/theorems/46a3fea6-e04d-4116-be9c-66f832031e24
-- title:
--   Farkas' lemma in inequality form
-- statement:
--   **(Theorem 4.7)** Suppose that the system of linear inequalities $Ax \le b$ has at least one solution, and let $d$ be some scalar. Then, the following are equivalent:
--
--   - **(a)** every feasible solution to the system $Ax \le b$ satisfies $c'x \le d$;
--   - **(b)** there exists some $p \ge 0$ such that $p'A = c'$ and $p'b \le d$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.7, p. 166

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.7 (p. 166).** For a solvable system `Ax ≤ b` and a
scalar `d`: every solution of `Ax ≤ b` satisfies `c'x ≤ d` iff some
`p ≥ 0` has `p'A = c'` and `p'b ≤ d`. -/

theorem LinearOptimization.farkas_inequality_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hfeas : ∃ x : Fin n → ℝ, A.mulVec x ≤ b) :
    (∀ x : Fin n → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) ↔
      ∃ p : Fin m → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  sorry
