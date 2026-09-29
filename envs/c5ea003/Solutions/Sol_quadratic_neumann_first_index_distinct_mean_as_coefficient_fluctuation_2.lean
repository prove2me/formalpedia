-- Prove2me | solution 2 for quadratic_neumann_first_index_distinct_mean_as_coefficient_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T03:08:34.488899+00:00
-- url     : https://prove2.me/submissions/b1c1b1dd-abe4-46d0-a23b-4e9881ec6e56

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannFirstIndexDistinctMeanContribution Omega S p =
      (1 - p) •
        centeredSamplingFluctuation Omega p
          (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) := by
  ext i j
  simp [quadraticNeumannFirstIndexDistinctMeanContribution,
    centeredSamplingFluctuation, samplingProjection,
    quadraticFirstIndexDistinctMeanCoefficientMatrix, Matrix.sum_apply]
  rw [Finset.sum_eq_single (i, j)]
  · simp
    by_cases hmem : (i, j) ∈ Omega
    · simp [hmem, centeredIndicator]
      by_cases hp : p = 0
      · simp [hp]
      · field_simp [hp]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = (i, j)
        · simp [hx]
        · have hxi : ¬ (i, j) = x := fun h => hx h.symm
          simp [hx, hxi, coordinateMatrix]
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
        · have hxi : ¬ (i, j) = x := fun h => hx h.symm
          simp [hx, hxi, coordinateMatrix]
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

