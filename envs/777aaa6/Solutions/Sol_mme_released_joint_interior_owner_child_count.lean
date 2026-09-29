-- Prove2me | solution 1 for mme_released_joint_interior_owner_child_count
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:31:24.740906+00:00
-- url     : https://prove2.me/submissions/f6a25423-20ad-4eda-9090-5f3e45ec63eb

import Definitions.Def_mme_released_joint_interior_frame
import Theorems.Thm_mme_recursive_split_coordinate_complement
import Theorems.Thm_mme_recursive_yz_count_full_cell

open MME MME.CompleteSplit MME.RecursiveYZ MME.ReleasedJointInterior

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

/-- Selecting one owner preserves every child-word count exactly, including
both halves of each parent. The equality can be used in either restriction direction. -/
theorem solution
    (k : ℕ) (j : Fin 270)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (f : ∀ r : Fin 6, Position (size r k) → CompleteWord 2)
    (r : Fin 6) (c : ReleasedInterior.Split (component j).2) (w : CompleteWord 2) :
    count (fullCell (ReleasedInterior.parent_total (component j).2)
      (fun r t => (splitEquiv r j).symm (a r j t)))
      (fun p => f p.1 ⟨j,p.2⟩) ⟨r,c⟩ w =
    count (fullCell (parent_total r) (a r)) (f r) ⟨j,splitEquiv r j c⟩ w := by
  classical
  rw [mme_recursive_yz_count_full_cell, mme_recursive_yz_count_full_cell]
  have heq (t : Fin (size r k j) × Fin 2) :
      (if t.2 = 0 then (splitEquiv r j).symm (a r j t.1)
       else complement (ReleasedInterior.parent_total (component j).2 r)
         ((splitEquiv r j).symm (a r j t.1))) = c ↔
      (if t.2 = 0 then a r j t.1
       else complement (parent_total r j) (a r j t.1)) = splitEquiv r j c := by
    split_ifs
    · exact (splitEquiv r j).symm_apply_eq
    · exact (Iff.of_eq (congrArg (fun d => d = c)
        (inverse_split_complement r j (a r j t.1)).symm)).trans
          (splitEquiv r j).symm_apply_eq
  have hcount : count
      (fun t : Fin (size r k j) × Fin 2 =>
        if t.2 = 0 then (splitEquiv r j).symm (a r j t.1)
        else complement (ReleasedInterior.parent_total (component j).2 r)
          ((splitEquiv r j).symm (a r j t.1)))
      (fun t => f r ⟨j,t⟩) c w =
      count (fun t : Fin (size r k j) × Fin 2 =>
        if t.2 = 0 then a r j t.1 else complement (parent_total r j) (a r j t.1))
        (fun t => f r ⟨j,t⟩) (splitEquiv r j c) w := by
    unfold count
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun _ => heq t)
  exact hcount


#print axioms solution
