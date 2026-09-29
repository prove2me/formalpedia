-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T14:39:00.090045+00:00
-- url     : https://prove2.me/submissions/bbc8ecc0-686b-42ea-98f7-5dac7a74b98a

import Definitions.Def_linear_neumann_offdiag_bernstein

open MatrixCompletion
open scoped BigOperators

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w : Fin n₁ × Fin n₂) :
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (linearNeumannOffDiagonalCoefficientBaseMatrix S w)) := by
  unfold linearNeumannOffDiagonalCoefficientMatrix matrixEntrySum
    centeredSamplingFluctuation samplingProjection
    linearNeumannOffDiagonalCoefficientBaseMatrix
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rcases u with ⟨i, j⟩
  by_cases h : (i, j) = w
  · simp [h]
  · simp [h, centeredIndicator]
    by_cases hmem : (i, j) ∈ Omega2
    · simp [hmem]
      ring_nf
      exact Or.inl trivial
    · simp [hmem]
      ring_nf
      exact Or.inl trivial
