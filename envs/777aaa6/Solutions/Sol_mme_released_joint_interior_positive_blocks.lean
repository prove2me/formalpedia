-- Prove2me | solution 1 for mme_released_joint_interior_positive_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:46:58.380983+00:00
-- url     : https://prove2.me/submissions/ffc73778-6728-4cce-8989-6d6297578e9a

import Definitions.Def_mme_released_joint_interior_frame

open scoped BigOperators
open MME MME.ReleasedJointInterior

/-- The released (1,1,6) component of owner zero gives positive mass in every
inner region, hence every positive replication has physical parent positions. -/
theorem solution
    (r : Fin 6) (k : ℕ) (hk : 0 < k) : 0 < blocks r k := by
  have hbase : ∀ r : Fin 6, 0 < weight 10 *
      ReleasedInterior.regionalSize (component 10).1 (component 10).2 r := by
    decide +kernel
  have hsize : 0 < size r k 10 := by
    change 0 < k * weight 10 *
      ReleasedInterior.regionalSize (component 10).1 (component 10).2 r
    rw [Nat.mul_assoc]
    exact Nat.mul_pos hk (hbase r)
  exact hsize.trans_le
    (Finset.single_le_sum (fun j _ => Nat.zero_le (size r k j)) (Finset.mem_univ 10))


#print axioms solution
