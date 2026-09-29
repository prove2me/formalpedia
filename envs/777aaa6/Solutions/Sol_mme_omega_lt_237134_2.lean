-- Prove2me | solution 2 for mme_omega_lt_237134
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:35:00.696386+00:00
-- url     : https://prove2.me/submissions/c50d5e1e-3786-40af-9009-39878ab2d818
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_fourth_fixed_tau_value_surplus
import Theorems.Thm_mme_more_asymmetry_237134_of_six_symmetric_surplus

universe u

open MME

theorem solution {K : Type u} [Field K] :
    matMulExp K < 237134 / 100000 := by
  exact mme_more_asymmetry_237134_of_six_symmetric_surplus
    mme_more_asymmetry_fourth_fixed_tau_value_surplus
