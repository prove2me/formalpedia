-- Prove2me | solution 1 for mme_released_global_graded_hashed_recursive_construction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T09:48:24.901533+00:00
-- url     : https://prove2.me/submissions/113e1021-fed2-4c33-a1ad-5ddca63c3853

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_caps_one
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false
theorem solution :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
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
                    5 ^ (∑ s, zCountAt (k^2) c s * Boundary.ones s)) * (R.a * R.b * R.c) : ℕ) : ℝ) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro o
    norm_num
  · intro eps heps hcaps k0
    exact mme_released_global_graded_hashed_recursive_construction_caps_one eps heps (fun o => by simpa using hcaps o) k0