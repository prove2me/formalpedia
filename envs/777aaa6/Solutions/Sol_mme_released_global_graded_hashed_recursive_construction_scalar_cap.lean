-- Prove2me | solution 1 for mme_released_global_graded_hashed_recursive_construction_scalar_cap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:54:40.53031+00:00
-- url     : https://prove2.me/submissions/9ac7587d-d4fb-4bcd-9583-cf26ab13ebdd

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_boundary_dimension_factor_power
import Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution :
    ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            1 ≤ (∏ c : Fin zCells,
                  ((Fintype.card {p : Fin (zCount (k^2) a) // zCellOf (k^2) a p = c}).factorial /
                    ∏ s, (zCountAt (k^2) c s).factorial) *
                  5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) * (R.a * R.b * R.c) ∧
            (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
              Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                Real.log (((∏ c : Fin zCells,
                  ((Fintype.card {p : Fin (zCount (k^2) a) // zCellOf (k^2) a p = c}).factorial /
                    ∏ s, (zCountAt (k^2) c s).factorial) *
                  5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) *
                    (R.a * R.b * R.c) : ℕ) : ℝ) := by
  intro e he0 he1 k0
  obtain ⟨k, hk0, H⟩ :=
    mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed e he0 he1 k0
  refine ⟨k, hk0, fun hk a ↦ ?_⟩
  obtain ⟨R, h1, habc, h3, h4⟩ := H hk a
  obtain ⟨hB1, hpow⟩ := mme_released_boundary_dimension_factor_power (k^2) hk a
  set B : ℕ := ∏ c : Fin zCells,
      ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
      5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) with hBdef
  set Z : ℕ := ∏ c : Fin zCells,
      ((Fintype.card {p : Fin (zCount (k^2) a) // zCellOf (k^2) a p = c}).factorial /
        ∏ s, (zCountAt (k^2) c s).factorial) *
      5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s) with hZdef
  clear_value B Z
  have hZ1 : 1 ≤ Z := le_trans (Nat.one_le_pow _ _ hB1) hpow
  refine ⟨R, h1, ?_, h3, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
    have hZpos : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZ1
    have habcpos : (0 : ℝ) < ((R.a * R.b * R.c : ℕ) : ℝ) := by exact_mod_cast habc
    have hlogZ : ((k^2 : ℕ) : ℝ) * Real.log (B : ℝ) ≤ Real.log (Z : ℝ) := by
      rw [← Real.log_pow]
      apply Real.log_le_log (pow_pos hBpos _)
      have := (Nat.cast_le (α := ℝ)).mpr hpow
      rwa [Nat.cast_pow] at this
    rw [Nat.cast_mul, Real.log_mul hZpos.ne' habcpos.ne']
    push_cast at hlogZ h4 ⊢
    linarith

