-- Prove2me | solution 1 for mme_CW_auxiliary_inequality_2376_profile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:56:40.410482+00:00
-- url     : https://prove2.me/submissions/0a7de22e-9ba6-44ce-87e6-7fae8b141ece
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_auxiliary_RHS_one_le
import Theorems.Thm_mme_CW_coupled_piece_value
import Theorems.Thm_mme_CW_square_laser_value_2376_of_coupled
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (homega : 2 ≤ matMulExp_strassen K) :
    auxiliaryRHS 6 (matMulExp_strassen K / 3)
        cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64 := by
  have htau : 2 ≤ 3 * (matMulExp_strassen K / 3) := by
    convert homega using 1 <;> ring
  have hcoupled := mme_CW_coupled_piece_value
    (K := K) 6 (by norm_num) (matMulExp_strassen K / 3) htau
  have hvalue := mme_CW_square_laser_value_2376_of_coupled
    (K := K) (matMulExp_strassen K / 3) htau hcoupled
  have hbound := mme_tau_value_le_of_asymptoticRank_le
    (by positivity)
    (mme_CW_auxiliary_RHS_one_le
      6 (by norm_num) (matMulExp_strassen K / 3) htau
      cw2376_a cw2376_b cw2376_c cw2376_d
      (by norm_num [cw2376_a])
      (by norm_num [cw2376_b])
      (by norm_num [cw2376_c])
      (by norm_num [cw2376_d])
      (by
        norm_num [cw2376_a, cw2376_b, cw2376_c, cw2376_d]
        rfl))
    (mme_CW_square_asymptoticRank_le (K := K) 6)
    hvalue
  norm_num at hbound ⊢
  exact hbound
