-- Prove2me | solution 2 for mme_schonhage_pan_Phi_coeff_twelve_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:09:43.818901+00:00
-- url     : https://prove2.me/submissions/66144000-ce0a-437a-9fb7-eaa6f36ec0ca

import Definitions.Def_mme_schonhage_pan_certificate
import Theorems.Thm_mme_schonhage_pan_Phi_coeff_repr
import Theorems.Thm_mme_schonhage_pan_fullPoly_coeff_twelve
import Theorems.Thm_mme_schonhage_pan_targetTensor_repr
import Theorems.Thm_mme_schonhage_pan_targetTensor_eq_Xobj_t

open MME PiTensorProduct BigOperators

universe u

theorem solution {K : Type u} [Field K] :
    (PanLeanBridge.Phi (K := K)).coeff 12 =
      (PanLeanBridge.Xobj (K := K)).t := by
  have htarget :
      (PanLeanBridge.Phi (K := K)).coeff 12 =
        PanLeanBridge.targetTensor (K := K) := by
    apply (PanLeanBridge.tensorBasis (K := K)).repr.injective
    ext q
    rw [mme_schonhage_pan_Phi_coeff_repr,
      mme_schonhage_pan_fullPoly_coeff_twelve,
      mme_schonhage_pan_targetTensor_repr]
  rw [htarget, mme_schonhage_pan_targetTensor_eq_Xobj_t]
