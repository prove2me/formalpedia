-- Prove2me | solution 1 for mme_released_joint_interior_common_mode_useful_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:16.389201+00:00
-- url     : https://prove2.me/submissions/7583bf16-b29e-4e2b-8203-e33bfbc682a0

import Theorems.Thm_mme_released_joint_interior_owner_useful

open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

/-- In common source mode order, the six joint exact histograms are equivalent
to all selected-owner exact histograms, including zero-sized owner labels. -/
theorem solution
    (k : ℕ) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2) :
    (∀ r : Fin 6, Useful (fullCell (parent_total r) (a r))
      (integerProfile r k ((roleEquiv r).symm i)) (f r)) ↔
    ∀ j : Fin 270,
      Useful (fullCell (ReleasedInterior.parent_total (component j).2)
        (fun r t => (splitEquiv r j).symm (a r j t)))
        (fun c w => k * weight j * ReleasedInterior.integerProfile
          (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
        (fun p => f p.1 ⟨j,p.2⟩) := by
  constructor
  · intro hu j
    apply mme_released_joint_interior_owner_useful
    intro r
    simpa only [orientation, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using hu r
  · intro hu r
    rintro ⟨j,c⟩ w
    have hc := hu j ⟨r,(splitEquiv r j).symm c⟩ w
    rw [mme_released_joint_interior_owner_child_count] at hc
    simpa only [integerProfile, Equiv.apply_symm_apply, orientation,
      Equiv.trans_apply, Equiv.symm_apply_apply] using hc


#print axioms solution
