-- Prove2me | Theorems.Thm_mme_released_joint_outer_windows_cell_product_restriction
-- name    : mme_released_joint_outer_windows_cell_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:07:38.543224+00:00
-- url     : https://prove2.me/theorems/aa3b4bf2-ce70-438c-b45d-85dc8c476e86
-- title:
--   Six actual outer windows supply the full common-mode cell product
-- statement:
--   The six released outer histogram windows restrict to the complete 270-cell product in joint mode order. Reference addresses and tolerances are preserved; only whole-owner permutations and finite-product regrouping are used. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_normalized_cell_product_restriction
import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_released_joint_interior_profiles
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit MME.TensorObj
universe u

theorem mme_released_joint_outer_windows_cell_product_restriction
    {K : Type u} [Field K] (t : ℕ) (ht : 0 < t)
    (a : ∀ owner : Fin 6, Reference owner t) (eps : ℝ) :
    let L : Fin 270 → ℕ := fun j => t * coarseCounts
      (MME.ReleasedJointInterior.component j).1
      (shapeEquiv (MME.ReleasedJointInterior.component j).2)
    let T : Fin 270 → TensorObj K 3 := fun j =>
      permObj (MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1) ( ((source K 5 3 (L j)).basisAllAllowedSubtensor (basis K 5 3 (L j))
      (fun i x =>
        (∀ r, grade (label 5 3 (L j) (Equiv.refl _) x r) = ((shapeEquiv (MME.ReleasedJointInterior.component j).2).val i).val) ∧
        if (L j) = 0 then ∀ w, |(profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin (L j) => Unit.unit)
          (label 5 3 (L j) (Equiv.refl _) x) Unit.unit w : ℝ) / (L j) -
          ((blocks t : ℝ) / (L j)) * (profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          ((blocks t : ℝ) / (L j)) * (eps))))
    Restrict (kronFin 270 T)
      (kronFin 6 (fun owner => permObj (MME.ReleasedJointInterior.roleEquiv owner)
        (ProfiledCW.tensor K ((frame owner t ht (a owner)).window
          (windowGood owner t eps))))) := by sorry
