-- Prove2me | solution 1 for mme_released_joint_interior_owner_reference_target
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:12:23.344275+00:00
-- url     : https://prove2.me/submissions/f1b2df05-70e1-4863-b2a5-6d8426d5c6b0

import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_recursive_x_hash_families

open MME MME.RecursiveYZ MME.ReleasedJointInterior

/-- A joint target address reconstructs the prescribed address histogram for
every owner-parent label, after undoing the joint split-coordinate permutation. -/
theorem solution
    (k : ℕ) (j : Fin 270)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (ha : ∀ r, a r ∈ RecursiveXHash.target (n := size r k) (splitCount r k)) :
    (fun r t => (splitEquiv r j).symm (a r j t)) ∈
      RecursiveXHash.target
        (n := fun r => k * weight j * ReleasedInterior.regionalSize
          (component j).1 (component j).2 r)
        (fun r c => k * weight j * ReleasedInterior.splitCount
          (component j).1 (component j).2 r c) := by
  classical
  unfold RecursiveXHash.target at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r c
  have hc : RecursiveThinSplit.count (a r j) ((splitEquiv r j) c) =
      splitCount r k j ((splitEquiv r j) c) := ha r j ((splitEquiv r j) c)
  change RecursiveThinSplit.count
    (fun t => (splitEquiv r j).symm (a r j t)) c = _
  have heq (t : Fin (size r k j)) :
      (splitEquiv r j).symm (a r j t) = c ↔ a r j t = (splitEquiv r j) c := by
    exact (splitEquiv r j).symm_apply_eq
  simpa only [RecursiveThinSplit.count, heq, splitCount, Equiv.symm_apply_apply] using hc


#print axioms solution
