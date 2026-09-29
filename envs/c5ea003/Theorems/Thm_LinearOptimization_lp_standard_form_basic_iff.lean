-- Prove2me | Theorems.Thm_LinearOptimization_lp_standard_form_basic_iff
-- name    : LinearOptimization.lp_standard_form_basic_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:46.888706+00:00
-- url     : https://prove2.me/theorems/cb64a364-800f-4b16-9200-2655d1da853e
-- title:
--   Basic solutions of standard-form polyhedra via basis columns
-- statement:
--   **(Theorem 2.4)** Consider the constraints $Ax = b$ and $x \ge 0$ and assume that the $m \times n$ matrix $A$ has linearly independent rows. A vector $x \in \mathbb{R}^n$ is a basic solution if and only if we have $Ax = b$, and there exist indices $B(1), \dots, B(m)$ such that:
--
--   - **(a)** The columns $A_{B(1)}, \dots, A_{B(m)}$ are linearly independent;
--   - **(b)** If $i \ne B(1), \dots, B(m)$, then $x_i = 0$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.4, p. 53

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_BasicSolution


open Matrix

/-- **B&T Theorem 2.4 (p. 53).** Characterization of basic solutions of the
standard-form system: under the book's explicit hypothesis that the rows of
`A` are linearly independent, `x` is a basic solution iff `Ax = b` and the
nonzero coordinates of `x` live inside some basis `B` (injective basic
indices with linearly independent basic columns). -/

theorem LinearOptimization.lp_standard_form_basic_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : LinearIndependent ℝ (fun i => A i))
    (x : Fin n → ℝ) :
    IsBasicSolution (stdFormSystem A b) x ↔
      A.mulVec x = b ∧ ∃ B : Fin m ↪ Fin n, IsStdBasis A B ∧
        ∀ j, j ∉ Set.range B → x j = 0 := by
  sorry
