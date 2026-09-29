-- Prove2me | solution 1 for mme_released_joint_interior_common_mode_graded_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:17:57.667726+00:00
-- url     : https://prove2.me/submissions/3fae4411-c3ba-4eaf-a9af-5234a5fa2538

import Theorems.Thm_mme_released_joint_interior_owner_graded

open scoped BigOperators
open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

/-- The joint and selected-owner child grades are equivalent when all tensors
are read in the same source mode order. -/
theorem solution
    (k : ℕ) (i : Fin 3)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2) :
    (∀ r : Fin 6, Graded (parent_total r) ((roleEquiv r).symm i) (a r) (f r)) ↔
    ∀ j : Fin 270,
      Graded (ReleasedInterior.parent_total (component j).2)
        ((roleEquiv (component j).1).symm i)
        (fun r t => (splitEquiv r j).symm (a r j t))
        (fun p => f p.1 ⟨j,p.2⟩) := by
  have hmode (j : Fin 270) (r : Fin 6) :
      (orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i) =
        (roleEquiv r).symm i := by
    simp only [orientation, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  constructor
  · intro hg j
    apply mme_released_joint_interior_owner_graded
    intro r
    rw [hmode]
    exact hg r
  · intro hg r
    rintro ⟨j,t,h⟩
    have hc := hg j ⟨r,t,h⟩
    fin_cases h
    · change (∑ q, (f r ⟨j,t,0⟩ q).val) =
        ((a r j t).val ((roleEquiv r).symm i)).val
      change (∑ q, (f r ⟨j,t,0⟩ q).val) =
        ((a r j t).val
          ((orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i))).val at hc
      rw [hmode j r] at hc
      exact hc
    · simp only [fullCell] at hc ⊢
      change (∑ q, (f r ⟨j,t,1⟩ q).val) =
        ReleasedInterior.parent (component j).2 0
          (orientation (component j).1 r ((roleEquiv r).symm i)) -
        ((a r j t).val ((roleEquiv r).symm i)).val
      change (∑ q, (f r ⟨j,t,1⟩ q).val) =
        ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i) -
        ((a r j t).val
          ((orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i))).val at hc
      rw [hmode j r] at hc
      simpa only [orientation, Equiv.trans_apply, Equiv.apply_symm_apply] using hc


#print axioms solution
