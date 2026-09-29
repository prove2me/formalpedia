-- Prove2me | solution 1 for mme_released_joint_interior_owner_graded
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:46:59.698215+00:00
-- url     : https://prove2.me/submissions/494aff53-4727-4981-bd02-fa337442d831

import Definitions.Def_mme_released_joint_interior_frame

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior

/-- The joint child grades, read in a fixed owner's mode order, are precisely
the grades of the owner's reconstructed regional address. -/
theorem solution
    (k : ℕ) (j : Fin 270) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (hg : ∀ r : Fin 6,
      Graded (parent_total r) ((orientation (component j).1 r).symm i) (a r) (f r)) :
    Graded (ReleasedInterior.parent_total (component j).2) i
      (fun r t => (splitEquiv r j).symm (a r j t))
      (fun p => f p.1 ⟨j,p.2⟩) := by
  rintro ⟨r,t,h⟩
  have hgrade := hg r ⟨j,t,h⟩
  fin_cases h
  · simpa only [fullCell, if_pos rfl] using hgrade
  · simp only [fullCell] at hgrade ⊢
    change (∑ q, (f r ⟨j,t,1⟩ q).val) =
      ReleasedInterior.parent (component j).2 r i -
        ((a r j t).val ((orientation (component j).1 r).symm i)).val
    change (∑ q, (f r ⟨j,t,1⟩ q).val) =
      ReleasedInterior.parent (component j).2 0
        (orientation (component j).1 r ((orientation (component j).1 r).symm i)) -
        ((a r j t).val ((orientation (component j).1 r).symm i)).val at hgrade
    simpa only [Equiv.apply_symm_apply] using hgrade


#print axioms solution
