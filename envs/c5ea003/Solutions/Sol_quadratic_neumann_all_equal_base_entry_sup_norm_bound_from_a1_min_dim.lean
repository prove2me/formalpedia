-- Prove2me | solution 1 for quadratic_neumann_all_equal_base_entry_sup_norm_bound_from_a1_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T18:40:49.252597+00:00
-- url     : https://prove2.me/submissions/20c0d9ac-5a1e-4625-8a75-f30d450f073c

import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveAllEqualBaseEntryA1Min

theorem entry_le_sup {n₁ n₂ : Nat} (X : RealMatrix n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n₂, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

end ProveAllEqualBaseEntryA1Min

open ProveAllEqualBaseEntryA1Min

theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2 := by
  obtain ⟨Cker, hCker, hker⟩ := tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
  refine ⟨Cker ^ 2, sq_pos_of_pos hCker, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1
  let signScale : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  let kerScale : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))
  have hsign_sup : entrySupNorm (signMatrix S) ≤ signScale := by
    dsimp [signScale]
    exact entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hsign_nonneg : 0 ≤ signScale := by
    dsimp [signScale]
    positivity
  have hker_nonneg : 0 ≤ kerScale := by
    dsimp [kerScale]
    positivity
  haveI : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  haveI : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  have hsign_entry : |signMatrix S i j| ≤ signScale :=
    le_trans (entry_le_sup (signMatrix S) i j) hsign_sup
  have hker_entry :
      |tangentCoordinateKernel S i j i j| ≤ kerScale := by
    dsimp [kerScale]
    exact hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j i j
  have hprod :
      |signMatrix S i j| *
          |tangentCoordinateKernel S i j i j| *
            |tangentCoordinateKernel S i j i j| ≤
        signScale * kerScale * kerScale := by
    have hfirst :
        |signMatrix S i j| * |tangentCoordinateKernel S i j i j| ≤
          signScale * kerScale :=
      mul_le_mul hsign_entry hker_entry (abs_nonneg _) hsign_nonneg
    exact mul_le_mul hfirst hker_entry (abs_nonneg _) (mul_nonneg hsign_nonneg hker_nonneg)
  calc
    |quadraticNeumannAllEqualBaseMatrix S i j|
        = |signMatrix S i j| *
            |tangentCoordinateKernel S i j i j| *
              |tangentCoordinateKernel S i j i j| := by
          simp [quadraticNeumannAllEqualBaseMatrix, linearNeumannDiagonalBaseMatrix,
            tangentDiagonalMultiplier, abs_mul, mul_assoc]
    _ ≤ signScale * kerScale * kerScale := hprod
    _ =
        Cker ^ 2 * μ₁ *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2 := by
          dsimp [signScale, kerScale]
          ring
