-- Prove2me | solution 1 for mme_dwz_prescribed_z_power_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T16:08:03.521852+00:00
-- url     : https://prove2.me/submissions/b2a87b13-fc57-420d-9283-d0390f89dc30

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

set_option autoImplicit false
set_option warningAsError true

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) :
    TensorObj.Restrict (prescribedZPower T bZ grade p m) (T.kronPow (p.length m)) := by
  classical
  exact (mme_basisZAllowedSubtensor_projection_certificate _
    (kronPowModeBasis T 2 bZ (p.length m)) (prescribedZWord grade p m)).1
