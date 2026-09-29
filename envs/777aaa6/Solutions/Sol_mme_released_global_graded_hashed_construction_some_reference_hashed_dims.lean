-- Prove2me | solution 1 for mme_released_global_graded_hashed_construction_some_reference_hashed_dims
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:04:41.066824+00:00
-- url     : https://prove2.me/submissions/60057755-776c-4431-8659-1c932d61c0ce

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_log_joint_recipe_g_stage_compose
import Theorems.Thm_mme_released_global_graded_hashed_level3_stage_level2_continuation
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
            (6 * blocks (k^2) : ℝ) * ((583785872051 : ℝ)/100000000000) ≤
              Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  intro e he0 he1
  obtain ⟨C, hC⟩ :=
    mme_released_global_graded_hashed_level3_stage_level2_continuation e he0 he1
  -- six part stages and one continuation, each with at most `(k+1)^C` types/inputs
  refine ⟨7 * C, fun k0 ↦ ?_⟩
  obtain ⟨k, hk0, hk⟩ := hC k0
  refine ⟨k, hk0, fun hkpos ↦ ?_⟩
  obtain ⟨a, size, positions, S, T, Q, hsource, htarget, steps, next,
    htypes, hrate3, hin1, hinC, habc, hrate2, hdims⟩ := hk hkpos
  obtain ⟨R, hR1, hRC, hRrate, hRa, hRb, hRc⟩ :=
    mme_log_joint_recipe_g_stage_compose (ell := 3) (by norm_num) size positions S T
      hsource steps htarget next ((k + 1) ^ C) ((k + 1) ^ C)
      ((6 * blocks (k^2) : ℝ) * ((7363871 : ℝ)/10000000))
      ((6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000))
      htypes hin1 hinC hrate3 hrate2
  refine ⟨a, R, hR1, ?_, ?_, ?_, ?_⟩
  · calc R.inputs ≤ ((k + 1) ^ C) ^ 6 * (k + 1) ^ C := hRC
      _ = (k + 1) ^ (7 * C) := by ring
  · rw [hRa, hRb, hRc]; exact habc
  · have hsplit : (6 * blocks (k^2) : ℝ) * ((13223547 : ℝ)/10000000) =
        (6 * blocks (k^2) : ℝ) * ((7363871 : ℝ)/10000000) +
          (6 * blocks (k^2) : ℝ) * ((5859676 : ℝ)/10000000) := by ring
    rw [hsplit]; exact hRrate
  · rw [hRa, hRb, hRc]; exact hdims
