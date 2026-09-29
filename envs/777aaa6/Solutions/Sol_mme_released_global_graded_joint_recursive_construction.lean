-- Prove2me | solution 1 for mme_released_global_graded_joint_recursive_construction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T18:15:06.486317+00:00
-- url     : https://prove2.me/submissions/a99ca15d-8b07-40a8-8a19-dc5c149241b0

import Mathlib
import Definitions.Def_mme_released_global_joint_interface
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_global_two_part_split_data
import Theorems.Thm_mme_exact_profile_boundary_end
import Theorems.Thm_mme_released_global_two_part_split_window
import Theorems.Thm_mme_released_global_graded_hashed_recursive_construction

open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RecursiveYZ.Boundary MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

namespace MME.ReleasedRecursive.GRC

/-- The boundary end of the boundary part, from the published exact-profile construction. -/
noncomputable def zEnd (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) :
    BoundaryEnd 3 (partSize k a 0) (QZero k a) :=
  (mme_exact_profile_boundary_end (zLen k a) (zCellOf k a) zZero zGradeAt
    (fun c ↦ zGrade_total (zCellIdx.symm c)) (fun c ↦ zMode_spec (zCellIdx.symm c))
    (zCountAt k) (zCount_total k hk a) (fun c s hs ↦ zCount_support k hk c s hs)).choose

theorem zEnd_dims (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k) :
    (zEnd k hk a).a * (zEnd k hk a).b * (zEnd k hk a).c =
      ∏ c : Fin zCells, ((Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c}).factorial /
        ∏ s, (zCountAt k c s).factorial) * 5 ^ (∑ s, zCountAt k c s * Boundary.ones s) :=
  (mme_exact_profile_boundary_end (zLen k a) (zCellOf k a) zZero zGradeAt
    (fun c ↦ zGrade_total (zCellIdx.symm c)) (fun c ↦ zMode_spec (zCellIdx.symm c))
    (zCountAt k) (zCount_total k hk a) (fun c s hs ↦ zCount_support k hk c s hs)).choose_spec

noncomputable def partPred (k : ℕ) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) : ∀ j : Fin 2, Predicate (partSize k a j)
  | 0 => QZero k a
  | 1 => QPos k a eps

noncomputable def partChild (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) (child : LogJointRecipeG (partSize k a 1) 3 (QPos k a eps)) :
    ∀ j : Fin 2, LogJointRecipeG (partSize k a j) 3 (partPred k a eps j)
  | 0 => LogJointRecipeG.base (LogRecipe.boundary (zEnd k hk a))
  | 1 => child

/-- The top partition of the joint window into boundary cells and hashed cells. -/
noncomputable def topPartition (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o)
    (child : LogJointRecipeG (partSize k a 1) 3 (QPos k a eps)) :
    LogJointRecipeG (4 * (6 * blocks k)) 3 (jointWindow k hk a eps) :=
  LogJointRecipeG.partition (partSize k a) (partPositions k a) (partPred k a eps)
    (fun i x h ↦ mme_released_global_two_part_split_window k hk a eps heps i x (h 0) (h 1))
    (partChild k hk a eps child)

theorem top_inputs (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o)
    (child : LogJointRecipeG (partSize k a 1) 3 (QPos k a eps)) :
    (topPartition k hk a eps heps child).inputs = child.inputs := by
  show ∏ j, (partChild k hk a eps child j).inputs = child.inputs
  rw [Fin.prod_univ_two]
  show LogRecipe.inputs (LogRecipe.boundary (zEnd k hk a)) * child.inputs = child.inputs
  simp [LogRecipe.inputs]

theorem top_logOutputs (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o)
    (child : LogJointRecipeG (partSize k a 1) 3 (QPos k a eps)) :
    (topPartition k hk a eps heps child).logOutputs = child.logOutputs := by
  show ∑ j, (partChild k hk a eps child j).logOutputs = child.logOutputs
  rw [Fin.sum_univ_two]
  show LogRecipe.logOutputs (LogRecipe.boundary (zEnd k hk a)) + child.logOutputs = child.logOutputs
  simp [LogRecipe.logOutputs]

theorem top_dims (k : ℕ) (hk : 0 < k) (a : ∀ o : Fin 6, Reference o k)
    (eps : Fin 6 → ℝ) (heps : ∀ o, 0 ≤ eps o)
    (child : LogJointRecipeG (partSize k a 1) 3 (QPos k a eps)) :
    (topPartition k hk a eps heps child).a * (topPartition k hk a eps heps child).b *
        (topPartition k hk a eps heps child).c =
      (∏ c : Fin zCells, ((Fintype.card {p : Fin (zCount k a) // zCellOf k a p = c}).factorial /
        ∏ s, (zCountAt k c s).factorial) * 5 ^ (∑ s, zCountAt k c s * Boundary.ones s)) *
        (child.a * child.b * child.c) := by
  rw [← zEnd_dims k hk a]
  show (∏ j, (partChild k hk a eps child j).dims.1) * (∏ j, (partChild k hk a eps child j).dims.2.1) *
      (∏ j, (partChild k hk a eps child j).dims.2.2) = _
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  show ((zEnd k hk a).a * child.dims.1) * ((zEnd k hk a).b * child.dims.2.1) *
      ((zEnd k hk a).c * child.dims.2.2) = _
  unfold LogJointRecipeG.a LogJointRecipeG.b LogJointRecipeG.c
  ring

end MME.ReleasedRecursive.GRC

open MME.ReleasedRecursive.GRC in
theorem solution :
    ∃ eta : Fin 6 → ℝ, (∀ o, 0 < eta o) ∧
      ∀ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) → (∀ o, eps o ≤ eta o) →
        ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
          ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
            ∃ R : LogJointRecipeG (4 * (6 * blocks (k^2))) 3 (jointWindow (k^2) hk a eps),
              1 ≤ R.inputs ∧ 1 ≤ R.a * R.b * R.c ∧
              (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
                Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
              (6 * blocks (k^2) : ℝ) *
                (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                  Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  obtain ⟨eta, heta, h⟩ := mme_released_global_graded_hashed_recursive_construction
  refine ⟨eta, heta, fun eps heps hle k0 ↦ ?_⟩
  obtain ⟨k, hk0, hR⟩ := h eps heps hle k0
  refine ⟨k, hk0, fun hk a ↦ ?_⟩
  obtain ⟨R, hin, hdim1, hrate, hdim⟩ := hR hk a
  have h0 : ∀ o, 0 ≤ eps o := fun o ↦ (heps o).le
  refine ⟨topPartition (k^2) hk a eps h0 R, ?_, ?_, ?_, ?_⟩
  · rw [top_inputs]; exact hin
  · rw [top_dims]; exact hdim1
  · rw [top_inputs, top_logOutputs]; exact hrate
  · rw [top_dims]; exact hdim
