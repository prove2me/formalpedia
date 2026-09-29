-- Prove2me | Theorems.Thm_LinearOptimization_farkas_lemma
-- name    : LinearOptimization.farkas_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T18:43:17.227743+00:00
-- url     : https://prove2.me/theorems/17b978fd-1695-42b9-aeb1-ae2830355f3c
-- title:
--   Farkas' lemma
-- statement:
--   **(Theorem 4.6, Farkas' lemma — GOAL)** Let $A$ be a matrix of dimensions $m \times n$ and let $b$ be a vector in $\mathbb{R}^m$. Then, exactly one of the following two alternatives holds:
--
--   - **(a)** there exists some $x \ge 0$ such that $Ax = b$;
--   - **(b)** there exists some vector $p$ such that $p'A \ge 0'$ and $p'b < 0$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.6, p. 165

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.6 (p. 165).** Farkas' lemma: exactly one of
(a) `∃ x ≥ 0, Ax = b` and (b) `∃ p, p'A ≥ 0' ∧ p'b < 0` holds. -/

theorem LinearOptimization.farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Xor' (∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ p : Fin m → ℝ, 0 ≤ Aᵀ.mulVec p ∧ p ⬝ᵥ b < 0) := by
  sorry
