-- Prove2me | solution 1 for mme_released_joint_interior_owner_useful
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:35.077567+00:00
-- url     : https://prove2.me/submissions/91369128-c717-4f57-80b3-e40d67bd1331

import Theorems.Thm_mme_released_joint_interior_owner_child_count

open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

/-- Exact joint child-word histograms restrict to the exact released histogram
of each owner, on its original physical positions and in its own mode order. -/
theorem solution
    (k : ℕ) (j : Fin 270) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (hu : ∀ r : Fin 6,
      Useful (fullCell (parent_total r) (a r))
        (integerProfile r k ((orientation (component j).1 r).symm i)) (f r)) :
    Useful (fullCell (ReleasedInterior.parent_total (component j).2)
      (fun r t => (splitEquiv r j).symm (a r j t)))
      (fun c w => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2 i c w)
      (fun p => f p.1 ⟨j,p.2⟩) := by
  rintro ⟨r,c⟩ w
  rw [mme_released_joint_interior_owner_child_count k j a f r c w]
  have hc := hu r ⟨j,splitEquiv r j c⟩ w
  simpa only [integerProfile, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hc


#print axioms solution
