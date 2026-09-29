-- Prove2me | solution 1 for mme_released_joint_interior_positive_cell_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:22.481638+00:00
-- url     : https://prove2.me/submissions/35f0c002-1cd7-40bd-b47e-bf7cce58a044

import Theorems.Thm_mme_released_global_common_mode_cell_window

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

-- Avoid unfolding the released tables merely to check binder names.
set_option linter.constructorNameAsVariable false in
/-- A positive joint label obtains exactly its common-mode owner window from
its normalized outer cell. Its physical length is the joint weight times the
released denominator, and the window keeps the joint positivity guard. -/
theorem solution
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
      (permObj (MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1) X) := by
  classical
  have hi : (ReleasedInterior.seed (MME.ReleasedJointInterior.component j).1
      (MME.ReleasedJointInterior.component j).2).boundary = [] := by
    by_contra hn
    simp only [MME.ReleasedJointInterior.weight, if_neg hn] at hw
    omega
  have hwEq : MME.ReleasedJointInterior.weight j =
      alpha (MME.ReleasedJointInterior.component j).1
        (MME.ReleasedJointInterior.component j).2 := by
    simp only [MME.ReleasedJointInterior.weight, if_pos hi]
  have ha : 0 < alpha (MME.ReleasedJointInterior.component j).1
      (MME.ReleasedJointInterior.component j).2 := hwEq ▸ hw
  have h := mme_released_global_common_mode_cell_window (K := K)
    (MME.ReleasedJointInterior.component j).1
    (MME.ReleasedJointInterior.component j).2 ha t ht eps heps
  have hL : t * coarseCounts (MME.ReleasedJointInterior.component j).1
      (shapeEquiv (MME.ReleasedJointInterior.component j).2) =
      t * MME.ReleasedJointInterior.weight j * denominator ^ 4 := by
    simp only [coarseCounts, Equiv.symm_apply_apply, ← hwEq, Nat.mul_assoc]
  rw [hL] at h
  simpa only [hw, true_implies] using h


#print axioms solution
