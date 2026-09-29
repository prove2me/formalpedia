-- Prove2me | solution 1 for mme_schonhage_pan_direct_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:06:29.443063+00:00
-- url     : https://prove2.me/submissions/3b28e76a-915e-4eeb-8113-e1fcdf73bdcd

import Theorems.Thm_mme_schonhage_pan_degenerates
import Theorems.Thm_mme_degenerates_asymptoticRank_le

open MME

universe u

theorem solution {K : Type u} [Field K] :
    tensorAsymptoticRank
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1]) ≤ 156 := by
  exact mme_degenerates_asymptoticRank_le mme_schonhage_pan_degenerates
