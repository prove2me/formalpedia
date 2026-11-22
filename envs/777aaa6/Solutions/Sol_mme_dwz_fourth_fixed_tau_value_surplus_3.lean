-- Prove2me | solution 3 for mme_dwz_fourth_fixed_tau_value_surplus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T18:41:03.25998+00:00
-- url     : https://prove2.me/submissions/3be19484-4eb3-4ccf-bf48-391a90158619
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_dwz_fourth_value_surplus_witness
import Theorems.Thm_mme_paired_Ctensor_certificate_to_six_symmetric_tau_value
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem solution {K : Type u} [Field K] :
    exists (V : Real),
      (2401 : Real) < V /\
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        (790643 / 1000000) V := by
  obtain ⟨A, H, volume, V, hgt, hlt, hcert⟩ := mme_dwz_fourth_value_surplus_witness (K := K)
  obtain ⟨stars⟩ := hcert
  have htau : (2 : Real) ≤ 3 * (790643 / 1000000 : Real) := by norm_num
  have hVnn : (0 : Real) ≤ V ^ 6 := by positivity
  have h := mme_paired_Ctensor_certificate_to_six_symmetric_tau_value stars
    (790643 / 1000000 : Real) htau (V ^ 6) hVnn hlt
  exact ⟨V, hgt, h⟩
