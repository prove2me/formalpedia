-- Prove2me | solution 1 for mme_released_global_graded_hashed_recursive_construction_caps_one
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T21:29:57.503363+00:00
-- url     : https://prove2.me/submissions/db8ccdd4-f6e3-4c1e-8548-1425c4798029

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_log_joint_recipe_g_source_mono
import Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution :
    (eps : Fin 6 → ℝ) → (∀ o, 0 < eps o) → (∀ o, eps o ≤ 1) →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a eps),
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
  intro eps heps hcap k0
  -- the smallest owner tolerance
  set e : ℝ := Finset.univ.inf' Finset.univ_nonempty eps with he
  have he_pos : 0 < e := (Finset.lt_inf'_iff _).2 (fun o _ ↦ heps o)
  have he_le : ∀ o, e ≤ eps o := fun o ↦ Finset.inf'_le _ (Finset.mem_univ o)
  obtain ⟨k, hk0, H⟩ :=
    mme_released_global_graded_hashed_recursive_construction_scalar_cap e he_pos
      ((he_le 0).trans (hcap 0)) k0
  refine ⟨k, hk0, fun hk a ↦ ?_⟩
  obtain ⟨R, h1, h2, h3, h4⟩ := H hk a
  -- the scalar window is contained in the owner-wise window
  have hmono : ∀ i y, QPos (k^2) a (fun _ ↦ e) i y → QPos (k^2) a eps i y := by
    intro i y hy
    exact ⟨hy.1, fun o c hc w ↦ (hy.2 o c hc w).trans (he_le o)⟩
  obtain ⟨R', g1, g2, g3⟩ := mme_log_joint_recipe_g_source_mono R _ hmono
  have ga : R'.a = R.a := by simp only [LogJointRecipeG.a, g3]
  have gb : R'.b = R.b := by simp only [LogJointRecipeG.b, g3]
  have gc : R'.c = R.c := by simp only [LogJointRecipeG.c, g3]
  refine ⟨R', ?_, ?_, ?_, ?_⟩
  · rw [g1]; exact h1
  · rw [ga, gb, gc]; exact h2
  · rw [g1, g2]; exact h3
  · rw [ga, gb, gc]; exact h4
