-- Prove2me | solution 1 for mme_released_joint_interior_complement_classification
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:23.319229+00:00
-- url     : https://prove2.me/submissions/011ccf83-e4ee-4135-b70a-a264f037d861

import Theorems.Thm_mme_released_interior_boundary_classification
import Definitions.Def_mme_released_joint_interior_profiles

set_option autoImplicit false
open MME.ReleasedJointInterior

/-- Every label omitted from the joint interior has either zero coarse mass or
an actual zero parent coordinate, so the empty-cell and boundary rates cover it. -/
theorem solution
    (j : Fin 270) (hj : ¬ 0 < weight j) :
    MME.ReleasedGlobal.coarseCounts (component j).1
        (MME.ReleasedGlobal.shapeEquiv (component j).2) = 0 ∨
      ∃ z : Fin 3, ((MME.ReleasedGlobal.shape (component j).2).val z).val = 0 := by
  classical
  by_cases hi : (MME.ReleasedInterior.seed (component j).1 (component j).2).boundary = []
  · left
    have ha : MME.ReleasedGlobal.alpha (component j).1 (component j).2 = 0 := by
      simpa only [weight, hi, if_true, Nat.not_lt, Nat.le_zero] using hj
    simp only [MME.ReleasedGlobal.coarseCounts, Equiv.symm_apply_apply, ha, zero_mul]
  · right
    have h := (mme_released_interior_boundary_classification (component j).1
      (component j).2).not.mp hi
    push_neg at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, Nat.eq_zero_of_le_zero hz⟩


#print axioms solution
