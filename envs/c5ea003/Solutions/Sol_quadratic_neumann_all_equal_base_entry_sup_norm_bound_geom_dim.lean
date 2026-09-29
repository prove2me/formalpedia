-- Prove2me | solution 1 for quadratic_neumann_all_equal_base_entry_sup_norm_bound_geom_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T12:40:35.348328+00:00
-- url     : https://prove2.me/submissions/7c66734e-2de8-4c37-a4f2-bd13d7bae1aa

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
import Theorems.Thm_entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds

open MatrixCompletion

/-- G2: honest geometric-mean entry bound for the all-equal base matrix. -/
theorem solution :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            ((↑(min n₁ n₂)) ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) := by
  obtain ⟨Cker, hCker, hker⟩ := tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  refine ⟨Cker ^ 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hminR : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by
    have : 0 < min n₁ n₂ := lt_min hn₁ hn₂
    exact_mod_cast this
  have hμ₀0 : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- sign bound (geometric) and kernel bound (min-dim)
  have hsign := entry_sup_norm_sign_matrix_bound_from_a0_geom_dim
    n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hkerS := hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hsign0 : (0 : ℝ) ≤ μ₀ * (r : ℝ) / Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) := by
    positivity
  have hker0 : (0 : ℝ) ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
    positivity
  have hcomp := entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
    hn₁ hn₂ S hsign0 hker0 hsign hkerS
  refine hcomp.trans_eq ?_
  have hsqrt : (0 : ℝ) < Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  field_simp
  try ring
