-- Prove2me | solution 1 for mme_released_joint_interior_owner_parent_typical
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:17:56.012143+00:00
-- url     : https://prove2.me/submissions/c047cda8-6bf1-4dc8-9c66-e7d3194bc6d4

import Theorems.Thm_mme_released_joint_interior_parent_mixture

open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior

/-- Reading all six joint regions in a fixed owner's coordinate order recovers
that owner's original parent-typical window for each parent shape. The same
physical child words are used on both sides. -/
theorem solution
    (k : ℕ) (j : Fin 270) (i : Fin 3) (eps : ℝ)
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (ht : ∀ r : Fin 6,
      parentTypical (parent_total r) (size r k) (splitCount r k)
        (integerProfile r k ((orientation (component j).1 r).symm i)) eps (f r)) :
    parentTypical (ReleasedInterior.parent_total (component j).2)
      (fun r => k * weight j * ReleasedInterior.regionalSize
        (component j).1 (component j).2 r)
      (fun r c => k * weight j * ReleasedInterior.splitCount
        (component j).1 (component j).2 r c)
      (fun c w => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2 i c w) eps
      (fun p => f p.1 ⟨j,p.2⟩) := by
  intro r w
  have h := ht r j w
  rw [mme_released_joint_interior_parent_mixture] at h
  simpa only [Equiv.apply_symm_apply] using h


#print axioms solution
