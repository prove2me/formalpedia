-- Prove2me | Theorems.Thm_Hadamard_odd_multiplier_exists
-- name    : Hadamard.odd_multiplier_exists
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:05:03.660459+00:00
-- url     : https://prove2.me/theorems/304080d5-831e-4353-8d64-a132bf567acd
-- title:
--   Hadamard matrices of order $4k$ for odd $k$
-- statement:
--   For every odd natural number $k$, there exists a real matrix $M$ of order $4k$ whose entries are $1$ or $-1$ and whose determinant satisfies
--
--   $$|\det M|=(4k)^{(4k)/2}.$$
--
--   This is the odd-multiplier restriction of the open Hadamard conjecture. The associated reduction recovers even multipliers by repeated order doubling and proves the zero-order case separately. The odd multipliers remain unbounded.
-- source:
--   Hadamard determinant formulation: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean, IsHadamard and HadamardConjecture. Tensor closure is the elementary construction proved here from Matrix.det_kronecker, Mathlib/LinearAlgebra/Matrix/Kronecker.lean at c5ea00351c28e24afc9f0f84379aa41082b1188f, https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/LinearAlgebra/Matrix/Kronecker.lean; the odd-multiplier statement is explicitly a restricted open case, not a claimed solved theorem.

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem Hadamard.odd_multiplier_exists (k : ℕ) (hk : Odd k) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
