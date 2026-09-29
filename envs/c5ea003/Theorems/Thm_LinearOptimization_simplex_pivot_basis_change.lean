-- Prove2me | Theorems.Thm_LinearOptimization_simplex_pivot_basis_change
-- name    : LinearOptimization.simplex_pivot_basis_change
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:23:39.946289+00:00
-- url     : https://prove2.me/theorems/c45aa11a-e3c0-42b1-8055-a1b6c8d2f32c
-- title:
--   A simplex pivot yields a new basic feasible solution with lower cost
-- statement:
--   **(Theorem 3.2)** In the setting of a simplex iteration — $x$ a nondegenerate basic feasible solution with basis matrix $B = [A_{B(1)} \cdots A_{B(m)}]$, $j$ a nonbasic index with $\bar{c}_j < 0$, $d$ the $j$th basic direction,
--
--   $$\theta^* = \min_{\{i : d_{B(i)} < 0\}} (-x_{B(i)}/d_{B(i)})$$
--
--   finite and attained at the index $\ell$ (so $d_{B(\ell)} < 0$), and $\bar{B}$ obtained from $B$ by replacing $A_{B(\ell)}$ with $A_j$ (Eqs. (3.3)–(3.4)):
--
--   - **(a)** the columns $A_{B(i)}$, $i \ne \ell$, and $A_j$ are linearly independent and, therefore, $\bar{B}$ is a basis matrix;
--   - **(b)** the vector $y = x + \theta^* d$ is a basic feasible solution associated with the basis matrix $\bar{B}$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 3.2, p. 89

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 3.2 (p. 89).** Basis change at a simplex pivot: with
entering index `j` (`c̄_j < 0`), exiting row `ℓ` attaining the ratio test,
and `B'` obtained from `B` by replacing `B(ℓ)` with `j`, the new basic
columns are linearly independent (so `B'` is a basis matrix), and
`y = x + θ* • d` is a basic feasible solution associated with `B'`. -/

theorem LinearOptimization.simplex_pivot_basis_change {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B B' : Fin m ↪ Fin n) (hB : IsStdBasis A B)
    (x : Fin n → ℝ) (hx : x ∈ stdPolyhedron A b)
    (hxB : ∀ j ∉ Set.range B, x j = 0)
    (hnd : ¬IsStdDegenerateBasicSolution A b x)
    (j : Fin n) (hj : j ∉ Set.range B) (hcj : reducedCost A c B j < 0)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B j ℓ)
    (hmin : ∀ i, 0 < pivotColumn A B j i →
      x (B ℓ) / pivotColumn A B j ℓ ≤ x (B i) / pivotColumn A B j i)
    (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) (hB'ℓ : B' ℓ = j) :
    IsStdBasis A B' ∧
    x + (x (B ℓ) / pivotColumn A B j ℓ) • basicDirection A B j ∈
      stdPolyhedron A b ∧
    ∀ k ∉ Set.range B',
      (x + (x (B ℓ) / pivotColumn A B j ℓ) • basicDirection A B j) k = 0 := by
  sorry
