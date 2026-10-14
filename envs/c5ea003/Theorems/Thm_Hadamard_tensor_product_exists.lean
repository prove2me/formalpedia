-- Prove2me | Theorems.Thm_Hadamard_tensor_product_exists
-- name    : Hadamard.tensor_product_exists
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T04:05:01.000602+00:00
-- url     : https://prove2.me/theorems/964927c3-443d-486b-9d76-3976d863ca7c
-- title:
--   Tensor products preserve the Hadamard determinant equality
-- statement:
--   Let $n,m$ be natural numbers and let $A$ and $B$ be real sign matrices of orders $n$ and $m$. Suppose
--
--   $$|\det A|=n^{n/2},\qquad |\det B|=m^{m/2}.$$
--
--   Then there exists a real sign matrix $C$ of order $nm$ with
--
--   $$|\det C|=(nm)^{nm/2}.$$
--
--   Both zero orders are allowed, with the empty determinant and $0^0$ interpreted as $1$. This is the multiplicative closure principle for the determinant formulation of Hadamard matrices, reusable for tensor constructions and order reductions.
-- source:
--   Hadamard determinant formulation: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean, IsHadamard and HadamardConjecture. Tensor closure is the elementary construction proved here from Matrix.det_kronecker, Mathlib/LinearAlgebra/Matrix/Kronecker.lean at c5ea00351c28e24afc9f0f84379aa41082b1188f, https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/LinearAlgebra/Matrix/Kronecker.lean; the odd-multiplier statement is explicitly a restricted open case, not a claimed solved theorem.

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

open scoped Kronecker

theorem Hadamard.tensor_product_exists (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, A i j ∈ ({1, -1} : Finset ℝ))
    (hB : ∀ i j, B i j ∈ ({1, -1} : Finset ℝ))
    (hdA : |A.det| = (n : ℝ) ^ ((n : ℝ) / 2))
    (hdB : |B.det| = (m : ℝ) ^ ((m : ℝ) / 2)) :
    ∃ C : Matrix (Fin (n * m)) (Fin (n * m)) ℝ,
      (∀ i j, C i j ∈ ({1, -1} : Finset ℝ)) ∧
      |C.det| = ((n * m : ℕ) : ℝ) ^ (((n * m : ℕ) : ℝ) / 2) := by sorry
