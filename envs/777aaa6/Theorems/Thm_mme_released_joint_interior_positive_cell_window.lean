-- Prove2me | Theorems.Thm_mme_released_joint_interior_positive_cell_window
-- name    : mme_released_joint_interior_positive_cell_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:07:35.617877+00:00
-- url     : https://prove2.me/theorems/3bcf3963-99e4-4cb7-a7ea-c79ec5e778cf
-- title:
--   Positive joint labels inherit the actual outer cell windows
-- statement:
--   Each positive joint owner label receives exactly its guarded common-mode histogram window from the normalized outer cell, at the physical length determined by its joint weight. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_common_mode_cell_window
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

theorem mme_released_joint_interior_positive_cell_window
    {K : Type u} [Field K] (j : Fin 270)
    (hw : 0 < MME.ReleasedJointInterior.weight j) (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L := t * MME.ReleasedJointInterior.weight j * denominator ^ 4
    let X : TensorObj K 3 := ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv (MME.ReleasedJointInterior.component j).2).val i).val) ∧
        if L = 0 then ∀ w, |(profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile (MME.ReleasedJointInterior.component j).1).2 i ⟨0,shapeEquiv (MME.ReleasedJointInterior.component j).2⟩ w| ≤
          ((blocks t : ℝ) / L) * (eps)))
    Restrict
      (ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      0 < MME.ReleasedJointInterior.weight j →
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ReleasedInterior.parent (MME.ReleasedJointInterior.component j).2 0 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i)) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows (MME.ReleasedJointInterior.component j).1 (MME.ReleasedJointInterior.component j).2).map
            (fun a => if atom a.1 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i) = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps))
      (permObj (MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1) X) := by sorry
