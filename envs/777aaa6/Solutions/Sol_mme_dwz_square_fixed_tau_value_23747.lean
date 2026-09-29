-- Prove2me | solution 1 for mme_dwz_square_fixed_tau_value_23747
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:18:44.651127+00:00
-- url     : https://prove2.me/submissions/b8f813e2-a1b9-4667-9fc2-6b7192474329

import Theorems.Thm_mme_dwz_square_equation25_table2_below
import Theorems.Thm_mme_dwz_square_table2_numeric_23747
import Theorems.Thm_mme_six_symmetric_tau_value_to_direct_of_iso
import Theorems.Thm_mme_CW_square_six_symmetrization_iso

open MME
open MME.DWZSquare

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution {K : Type u} [Field K] :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23747 / 30000) (640001 / 10000) := by
  apply mme_six_symmetric_tau_value_to_direct_of_iso
  · norm_num
  · exact mme_CW_square_six_symmetrization_iso 6
  · apply mme_dwz_square_equation25_table2_below
    · norm_num
    · norm_num
    · exact mme_dwz_square_table2_numeric_23747
