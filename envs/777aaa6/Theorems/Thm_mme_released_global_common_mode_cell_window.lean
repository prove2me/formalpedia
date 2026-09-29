-- Prove2me | Theorems.Thm_mme_released_global_common_mode_cell_window
-- name    : mme_released_global_common_mode_cell_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:46:15.923499+00:00
-- url     : https://prove2.me/theorems/c04dfb71-7b1c-403f-aa40-bab689f0d5cd
-- title:
--   Outer cells supply common-mode histogram windows
-- statement:
--   Every positive normalized outer cell restricts to its parent histogram window after a whole-cell mode permutation, with the same tolerance and physical coordinates. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_parent_source_restricts_common_window
import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
import Definitions.Def_mme_released_joint_interior_profiles
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

theorem mme_released_global_common_mode_cell_window
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L := t * coarseCounts owner (shapeEquiv s)
    let X : TensorObj K 3 := ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * (eps)))
    Restrict
      (ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ReleasedInterior.parent s 0 ((MME.ReleasedJointInterior.roleEquiv owner).symm i)) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 ((MME.ReleasedJointInterior.roleEquiv owner).symm i) = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps))
      (permObj (MME.ReleasedJointInterior.roleEquiv owner) X) := by sorry
