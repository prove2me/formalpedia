-- Prove2me | solution 1 for mme_released_joint_interior_cells_keep_complement
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:33:07.275147+00:00
-- url     : https://prove2.me/submissions/13767160-4a2c-4d4f-8a03-09094aa30237

import Theorems.Thm_mme_released_joint_interior_positive_cell_window
import Theorems.Thm_mme_kronFin_restrict_keep_complement
import Theorems.Thm_mme_profiled_CW_empty_isomorphic

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj
universe u

-- Avoid unfolding the released tables merely to check binder names.
set_option linter.constructorNameAsVariable false in
/-- The complete common-mode outer cell product supplies the joint interior
windows together with every complementary cell. Boundary parents remain as
actual factors; zero joint labels contribute scalar units to the interior. -/
theorem solution
    {K : Type u} [Field K] (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
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
    let P : ∀ j : Fin 270, ProfiledCW.Predicate
        ((t * MME.ReleasedJointInterior.weight j * denominator ^ 4) * 4) :=
      fun j => (fun i (x : ProfiledCW.FineWord ((t * MME.ReleasedJointInterior.weight j * denominator ^ 4) * 4)) =>
      0 < MME.ReleasedJointInterior.weight j →
      (∀ p : Fin (t * MME.ReleasedJointInterior.weight j * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ReleasedInterior.parent (MME.ReleasedJointInterior.component j).2 0 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i)) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (t * MME.ReleasedJointInterior.weight j * denominator ^ 4) //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / (t * MME.ReleasedJointInterior.weight j * denominator ^ 4 : ℕ) -
          ((((jointRows (MME.ReleasedJointInterior.component j).1 (MME.ReleasedJointInterior.component j).2).map
            (fun a => if atom a.1 ((MME.ReleasedJointInterior.roleEquiv (MME.ReleasedJointInterior.component j).1).symm i) = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps)
    Restrict
      (kron (kronFin 270 (fun j => ProfiledCW.tensor K (P j)))
        (kronFin 270 (fun j => if 0 < MME.ReleasedJointInterior.weight j
          then oneObj else T j)))
      (kronFin 270 T) := by
  classical
  intro L T P
  apply mme_kronFin_restrict_keep_complement
  · intro j hw
    have hi : (ReleasedInterior.seed (MME.ReleasedJointInterior.component j).1
        (MME.ReleasedJointInterior.component j).2).boundary = [] := by
      by_contra hn
      simp only [MME.ReleasedJointInterior.weight, if_neg hn] at hw
      omega
    have hwEq : MME.ReleasedJointInterior.weight j =
        alpha (MME.ReleasedJointInterior.component j).1
          (MME.ReleasedJointInterior.component j).2 := by
      simp only [MME.ReleasedJointInterior.weight, if_pos hi]
    have hL : L j = t * MME.ReleasedJointInterior.weight j * denominator ^ 4 := by
      simp only [L, coarseCounts, Equiv.symm_apply_apply, ← hwEq, Nat.mul_assoc]
    have h := mme_released_joint_interior_positive_cell_window
      (K := K) j hw t ht eps heps
    dsimp only [T]
    rw [hL]
    exact h
  · intro j hw
    have hz : MME.ReleasedJointInterior.weight j = 0 := Nat.eq_zero_of_not_pos hw
    apply mme_profiled_CW_empty_isomorphic (by simp only [hz, mul_zero, zero_mul])
    intro i x hp
    exact (hw hp).elim


#print axioms solution
