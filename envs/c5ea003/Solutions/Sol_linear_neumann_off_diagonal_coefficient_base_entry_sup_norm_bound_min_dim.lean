-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T18:05:16.6966+00:00
-- url     : https://prove2.me/submissions/f79e1541-c50a-4d7b-bfd3-0ef6fa43a4ef

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveLinearOffdiagBaseEntryMin

theorem entry_le_sup {n₁ n₂ : Nat} (X : RealMatrix n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n₂, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

end ProveLinearOffdiagBaseEntryMin

open ProveLinearOffdiagBaseEntryMin

theorem solution :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          entrySupNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cker, hCker, hker⟩ := tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
  refine ⟨Cker, hCker, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
  have hsign_sup :
      entrySupNorm (signMatrix S) ≤
        μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hsign_rhs_nonneg :
      0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    positivity
  have hker_rhs_nonneg :
      0 ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
    positivity
  haveI : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  haveI : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  unfold entrySupNorm
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  by_cases hdiag : (i, j) = w
  · simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag]
    positivity
  · have hsign_entry :
        |signMatrix S i j| ≤
          μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
      le_trans (entry_le_sup (signMatrix S) i j) hsign_sup
    have hker_entry :
        |tangentCoordinateKernel S i j w.1 w.2| ≤
          Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) :=
      hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j w.1 w.2
    have hprod :
        |signMatrix S i j| * |tangentCoordinateKernel S i j w.1 w.2| ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) :=
      mul_le_mul hsign_entry hker_entry (abs_nonneg _) hsign_rhs_nonneg
    calc
      |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j|
          = |signMatrix S i j| * |tangentCoordinateKernel S i j w.1 w.2| := by
            simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag, abs_mul]
      _ ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := hprod
      _ =
          Cker * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
            ring
