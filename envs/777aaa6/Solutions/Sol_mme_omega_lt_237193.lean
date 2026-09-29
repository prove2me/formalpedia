-- Prove2me | solution 1 for mme_omega_lt_237193
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T16:06:23.844866+00:00
-- url     : https://prove2.me/submissions/dbfc94f3-7299-4607-bdff-67841cda0f71

import Theorems.Thm_mme_dwz_fourth_fixed_tau_value_surplus
import Theorems.Thm_mme_dwz_fourth_237193_of_six_symmetric_surplus

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    matMulExp K < 237193 / 100000 := by
  exact mme_dwz_fourth_237193_of_six_symmetric_surplus
    (mme_dwz_fourth_fixed_tau_value_surplus (K := K))
