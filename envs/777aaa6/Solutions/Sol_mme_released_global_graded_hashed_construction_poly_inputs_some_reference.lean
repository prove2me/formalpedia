-- Prove2me | solution 1 for mme_released_global_graded_hashed_construction_poly_inputs_some_reference
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:52:55.575003+00:00
-- url     : https://prove2.me/submissions/91b22353-c4d1-4bfe-af70-d4d0c104a9cd

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_boundary_unit_factor_log_lower
import Theorems.Thm_mme_released_global_graded_hashed_construction_some_reference_hashed_dims
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2), ∃ a : ∀ o : Fin 6, Reference o (k^2),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            R.inputs ≤ (k + 1) ^ C ∧
            1 ≤ R.a * R.b * R.c ∧
            (6 * blocks (k^2) : ℝ) * ((13223547 : ℝ)/10000000) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                (k^2 : ℝ) * Real.log ((∏ c : Fin zCells,
                  ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
                  5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) +
                Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  intro e he0 he1
  obtain ⟨C, hC⟩ :=
    mme_released_global_graded_hashed_construction_some_reference_hashed_dims e he0 he1
  refine ⟨C, fun k0 ↦ ?_⟩
  obtain ⟨k, hk0, hk⟩ := hC k0
  refine ⟨k, hk0, fun hkpos ↦ ?_⟩
  obtain ⟨a, R, h1, h2, h3, h4, h5⟩ := hk hkpos
  refine ⟨a, R, h1, h2, h3, h4, ?_⟩
  have hB := mme_released_boundary_unit_factor_log_lower
  -- The boundary factor and the block count are abstracted as opaque reals.
  generalize Real.log ((∏ c : Fin zCells,
      ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
      5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) = LB at hB ⊢
  generalize Real.log ((R.a * R.b * R.c : ℕ) : ℝ) = L at h5 ⊢
  have hblk : (blocks (k^2) : ℝ) = (blocks 1 : ℝ) * (k : ℝ)^2 := by
    unfold blocks; push_cast; ring
  rw [hblk] at h5 ⊢
  generalize (blocks 1 : ℝ) = X at hB h5 ⊢
  have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hB hk2
  nlinarith [hmul, h5]
