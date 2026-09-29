-- Prove2me | solution 1 for mme_CW_square_laser_value_of_coupled
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:45:39.604199+00:00
-- url     : https://prove2.me/submissions/fea61c80-a824-48f5-a602-001468d0b67d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_auxiliary_RHS_one_le
import Theorems.Thm_mme_CW_square_laser_frequent_witness_of_coupled

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K q) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (q : ℝ) ^ tau *
         (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K q) (CWObj K q)) tau
      (auxiliaryRHS q tau a b c d) := by
  refine ⟨?_, ?_⟩
  · have hone := mme_CW_auxiliary_RHS_one_le
      q hq tau htau a b c d ha hb hc hd hnorm
    linarith
  · exact mme_CW_square_laser_frequent_witness_of_coupled
      q hq tau htau a b c d ha hb hc hd hnorm hcoupled

