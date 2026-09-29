-- Prove2me | solution 1 for mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:13:16.433621+00:00
-- url     : https://prove2.me/submissions/a4c43b54-8eb1-461e-bf8b-61f0f5c308d7

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_hashed_recipe_reference_transport
import Theorems.Thm_mme_released_global_graded_hashed_construction_poly_inputs_some_reference
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution :
    ∀ e : ℝ, 0 < e → e ≤ 1 → ∃ C : ℕ,
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
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
    mme_released_global_graded_hashed_construction_poly_inputs_some_reference e he0 he1
  refine ⟨C, fun k0 ↦ ?_⟩
  obtain ⟨k, hk0, hk⟩ := hC k0
  refine ⟨k, hk0, fun hkpos a ↦ ?_⟩
  obtain ⟨a', R, h1, h2, h3, h4, h5⟩ := hk hkpos
  obtain ⟨R', hin, hout, hdims⟩ :=
    mme_released_hashed_recipe_reference_transport (k^2) 3 a a' (fun _ ↦ e) R
  have habc : R'.a * R'.b * R'.c = R.a * R.b * R.c := by
    simp only [LogJointRecipeG.a, LogJointRecipeG.b, LogJointRecipeG.c, hdims]
  refine ⟨R', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact h1
  · rw [hin]; exact h2
  · rw [habc]; exact h3
  · rw [hout]; exact h4
  · rw [habc]; exact h5
