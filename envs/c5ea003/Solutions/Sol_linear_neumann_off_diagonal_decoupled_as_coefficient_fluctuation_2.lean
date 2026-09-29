-- Prove2me | solution 2 for linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:32.568756+00:00
-- url     : https://prove2.me/submissions/3b2cb218-5458-4898-a4c5-4b5dfceb2459

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega1 Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) :
    linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S p =
      centeredSamplingFluctuation Omega1 p
        (linearNeumannOffDiagonalCoefficientMatrix Omega2 S p) := by
  ext i j
  simp [linearNeumannOffDiagonalDecoupledContribution,
    centeredSamplingFluctuation, samplingProjection,
    linearNeumannOffDiagonalCoefficientMatrix, Matrix.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp
    by_cases hmem : (i, j) ∈ Omega1
    · simp [hmem, centeredIndicator]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp [hp]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = (i, j)
        · simp [hx]
        · by_cases hxmem : x ∈ Omega2
          · have hxi : ¬ (i, j) = x := fun h => hx h.symm
            simp [hx, hxi, hxmem, coordinateMatrix]
            ring_nf
          · have hxi : ¬ (i, j) = x := fun h => hx h.symm
            simp [hx, hxi, hxmem, coordinateMatrix]
            ring_nf
    · simp [hmem, centeredIndicator]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp [hp]
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = (i, j)
        · simp [hx]
        · by_cases hxmem : x ∈ Omega2
          · have hxi : ¬ (i, j) = x := fun h => hx h.symm
            simp [hx, hxi, hxmem, coordinateMatrix]
            ring_nf
          · have hxi : ¬ (i, j) = x := fun h => hx h.symm
            simp [hx, hxi, hxmem, coordinateMatrix]
            ring_nf
  · intro x _ hx
    have hneq : ¬(i = x.1 ∧ j = x.2) := by
      intro h
      apply hx
      ext <;> simp [h.1, h.2]
    have hcoord : coordinateMatrix x.1 x.2 i j = 0 := by
      simp [coordinateMatrix, hneq]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, hcoord]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))
