-- Prove2me | solution 1 for mme_CW_square_laser_value_2376_of_coupled
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:54:58.447853+00:00
-- url     : https://prove2.me/submissions/1eacf81a-65a8-42e4-8862-45edd8ed90a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_auxiliary_RHS_one_le
import Theorems.Thm_mme_CW_square_laser_2376_cofinal_extraction_of_coupled
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_kron_self_kronPow_isomorphic

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K 6) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (6 : ℝ) ^ tau *
         (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau
      (auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) := by
  have ha : 0 < cw2376_a := by norm_num [cw2376_a]
  have hb : 0 < cw2376_b := by norm_num [cw2376_b]
  have hc : 0 < cw2376_c := by norm_num [cw2376_c]
  have hd : 0 < cw2376_d := by norm_num [cw2376_d]
  have hnorm :
      3 * cw2376_a + 6 * cw2376_b +
          3 * cw2376_c + 3 * cw2376_d = 1 := by
    norm_num [cw2376_a, cw2376_b, cw2376_c, cw2376_d] <;> rfl
  have hVone :
      1 ≤ auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d :=
    mme_CW_auxiliary_RHS_one_le
      6 (by norm_num) tau htau
      cw2376_a cw2376_b cw2376_c cw2376_d
      ha hb hc hd hnorm
  obtain ⟨m, error, hm, herror, hextract⟩ :=
    mme_CW_square_laser_2376_cofinal_extraction_of_coupled
      (K := K) tau htau hcoupled
  let s : ℕ → ℕ := fun n => 3000000 * m n
  have hs : Tendsto s atTop atTop := by
    dsimp [s]
    exact hm.nsmul_atTop (by norm_num)
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau
    (auxiliaryRHS 6 tau cw2376_a cw2376_b cw2376_c cw2376_d)
    (by linarith) s hs error herror
  filter_upwards [hextract] with n hn
  obtain ⟨k, x, y, z, hrestrict, hweight⟩ := hn
  refine ⟨k, x, y, z, ?_, ?_⟩
  · have hiso := mme_kron_self_kronPow_isomorphic
      (CWObj K 6) (3000000 * m n)
    apply TensorObj.Restrict.trans ?_ hiso.2
    simpa only [show 2 * (3000000 * m n) = 6000000 * m n by omega] using hrestrict
  · simpa only [s] using hweight
