-- Prove2me | Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype
-- name    : LinearOptimization.farkas_inequality_form_fintype
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T21:03:03.724166+00:00
-- url     : https://prove2.me/theorems/b8bf850e-4286-4f37-a220-9dc538db12fb
-- title:
--   Farkas' inequality theorem for an arbitrary finite constraint index
-- statement:
--   Let $I$ be an arbitrary finite index set of linear inequalities. Given row vectors $A_i\in\mathbb R^n$, scalars $b_i$, a cost vector $c\in\mathbb R^n$, and $d\in\mathbb R$, assume that the system $A_ix\le b_i$ for all $i\in I$ is feasible. Then the following are equivalent:
--
--   $$
--   \forall x,\quad (\forall i\in I,\ A_ix\le b_i)\Longrightarrow c'x\le d,
--   $$
--
--   and
--
--   $$
--   \exists p\in\mathbb R^I,\quad p\ge0,\qquad
--   \sum_{i\in I}p_iA_i=c',\qquad
--   \sum_{i\in I}p_ib_i\le d.
--   $$
--
--   This is the finite-index-set form of the theorem of alternatives for inequality systems. It allows downstream formalizations to use naturally structured finite constraint types without first encoding them arithmetically as `Fin m`.
--
--   **Formalization Note** This has exactly the mathematical content of `LinearOptimization.farkas_inequality_form`; only the finite row index type is generalized.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.7, p. 166; purely formal finite-index reindexing of the proved Fin m statement

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Matrix

theorem LinearOptimization.farkas_inequality_form_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hfeas : ∃ x : Fin n → ℝ, A.mulVec x ≤ b) :
    (∀ x : Fin n → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) ↔
      ∃ p : ι → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  sorry
