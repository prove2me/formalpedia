-- Prove2me | solution 1 for mme_omega_lt_237134
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:02:37.983502+00:00
-- url     : https://prove2.me/submissions/dd694aad-c55d-4a46-b271-64122a4e4e13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_fourth_fixed_tau_value_surplus
import Theorems.Thm_mme_more_asymmetry_237134_of_six_symmetric_surplus

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

-- Root reduction only: the imported fixed-tau surplus is a public Open child.
theorem solution {K : Type u} [Field K] :
    matMulExp K < 237134 / 100000 := by
  exact mme_more_asymmetry_237134_of_six_symmetric_surplus
    (mme_more_asymmetry_fourth_fixed_tau_value_surplus (K := K))
