-- Prove2me | solution 1 for mme_released_joint_interior_parent_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:05.495999+00:00
-- url     : https://prove2.me/submissions/2a2a4947-c7af-4d5e-8bbd-5cef6b0568e3

import Definitions.Def_mme_released_joint_interior_frame
import Theorems.Thm_mme_recursive_split_coordinate_complement

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior

private theorem inverse_split_complement (r : Fin 6) (j : Fin 270)
    (c : RecursiveThinSplit.Split 4 (parent r j)) :
    (splitEquiv r j).symm (complement (parent_total r j) c) =
      complement (ReleasedInterior.parent_total (component j).2 r)
        ((splitEquiv r j).symm c) := by
  apply (splitEquiv r j).injective
  rw [Equiv.apply_symm_apply]
  have h := mme_recursive_split_coordinate_complement
    (ReleasedInterior.parent (component j).2 0)
    (ReleasedInterior.parent_total (component j).2 r)
    (orientation (component j).1 r) ((splitEquiv r j).symm c)
  change splitEquiv r j
      (complement (ReleasedInterior.parent_total (component j).2 r)
        ((splitEquiv r j).symm c)) =
    complement (parent_total r j) (splitEquiv r j ((splitEquiv r j).symm c)) at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The common inner orientation changes only the names of split coordinates.
For each owner and parent label its parent-mixture center is exactly the original
scaled regional center, evaluated in the corresponding owner mode. -/
theorem solution
    (r : Fin 6) (k : ℕ) (i : Fin 3) (j : Fin 270)
    (w : Fin 2 → CompleteWord 2) :
    parentMixture (parent_total r) (size r k) (splitCount r k)
      (integerProfile r k i) j w =
    parentMixture (ReleasedInterior.parent_total (component j).2)
      (fun s => k * weight j * ReleasedInterior.regionalSize
        (component j).1 (component j).2 s)
      (fun s c => k * weight j * ReleasedInterior.splitCount
        (component j).1 (component j).2 s c)
      (fun c v => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2
        (orientation (component j).1 r i) c v) r w := by
  unfold parentMixture
  congr 1
  change (∑ c, (k * weight j * ReleasedInterior.splitCount
      (component j).1 (component j).2 r ((splitEquiv r j).symm c) : ℕ) *
      cellFrequency (integerProfile r k i) ⟨j,c⟩ (w 0) *
      cellFrequency (integerProfile r k i) ⟨j,complement (parent_total r j) c⟩ (w 1)) = _
  simp only [cellFrequency, integerProfile, inverse_split_complement]
  exact Equiv.sum_comp (splitEquiv r j).symm (fun c =>
    ((k * weight j * ReleasedInterior.splitCount
      (component j).1 (component j).2 r c : ℕ) : ℝ) *
      cellFrequency (fun c v => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2
        (orientation (component j).1 r i) c v) ⟨r,c⟩ (w 0) *
      cellFrequency (fun c v => k * weight j * ReleasedInterior.integerProfile
        (component j).1 (component j).2
        (orientation (component j).1 r i) c v)
        ⟨r,complement (ReleasedInterior.parent_total (component j).2 r) c⟩ (w 1))


#print axioms solution
