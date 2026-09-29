-- Prove2me | solution 1 for entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T15:11:31.377102+00:00
-- url     : https://prove2.me/submissions/c377b2cf-be9d-40ee-873b-27f3bd2cc5bd

import Mathlib.Data.Fintype.Order
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion
open scoped Classical BigOperators

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma abs_entry_le_entrySupNorm {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  exact Finite.le_ciSup_of_le i (Finite.le_ciSup_of_le j le_rfl)

/-- Entrywise algebra for the all-equal quadratic base matrix. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (S : SVD M r)
    {signBound kernelBound : ℝ} :
    0 ≤ signBound →
    0 ≤ kernelBound →
    entrySupNorm (signMatrix S) ≤ signBound →
    (∀ i j, |tangentCoordinateKernel S i j i j| ≤ kernelBound) →
    entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
      signBound * kernelBound ^ 2 := by
  intro hsign_nonneg hkernel_nonneg hsign hk
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  unfold quadraticNeumannAllEqualBaseMatrix linearNeumannDiagonalBaseMatrix tangentDiagonalMultiplier
  have hsign_entry : |signMatrix S i j| ≤ signBound :=
    (abs_entry_le_entrySupNorm (signMatrix S) i j).trans hsign
  have hkij : |tangentCoordinateKernel S i j i j| ≤ kernelBound := hk i j
  calc
    |(signMatrix S i j * tangentCoordinateKernel S i j i j) *
        tangentCoordinateKernel S i j i j|
        = |signMatrix S i j| * |tangentCoordinateKernel S i j i j| *
            |tangentCoordinateKernel S i j i j| := by rw [abs_mul, abs_mul]
    _ ≤ signBound * kernelBound * kernelBound := by
      have hprod1 :
          |signMatrix S i j| * |tangentCoordinateKernel S i j i j| ≤
            signBound * kernelBound :=
        mul_le_mul hsign_entry hkij (abs_nonneg _) hsign_nonneg
      exact mul_le_mul hprod1 hkij (abs_nonneg _)
        (mul_nonneg hsign_nonneg hkernel_nonneg)
    _ = signBound * kernelBound ^ 2 := by ring
