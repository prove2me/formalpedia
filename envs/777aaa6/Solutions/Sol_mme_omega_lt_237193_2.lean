-- Prove2me | solution 2 for mme_omega_lt_237193
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:34:50.373285+00:00
-- url     : https://prove2.me/submissions/cebcde3e-d77a-4c1b-aac4-31eb70039fe7

import Theorems.Thm_mme_dwz_fourth_fixed_tau_value_surplus
import Theorems.Thm_mme_dwz_fourth_237193_of_six_symmetric_surplus

universe u

open MME

theorem solution {K : Type u} [Field K] :
    matMulExp K < 237193 / 100000 := by
  exact mme_dwz_fourth_237193_of_six_symmetric_surplus
    mme_dwz_fourth_fixed_tau_value_surplus
