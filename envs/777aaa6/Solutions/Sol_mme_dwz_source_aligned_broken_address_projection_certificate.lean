-- Prove2me | solution 1 for mme_dwz_source_aligned_broken_address_projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:59:50.769626+00:00
-- url     : https://prove2.me/submissions/84bf8b42-3d73-4afe-9abe-cd547ca89272

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module

universe u

open MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    TensorObj.Restrict (brokenAddressObj K m outer copy)
        (coarseAddressObj K outer) ∧
      (brokenAddressGrading K m outer copy).classOf 0 0 = ⊤ ∧
      (brokenAddressGrading K m outer copy).classOf 1 0 = ⊤ ∧
      (brokenAddressGrading K m outer copy).classOf 2 0 =
        Submodule.span K
          (coarseAddressZBasis K outer ''
            {W | addressWordSurvives m outer copy W}) := by
  classical
  simpa only [brokenAddressObj, brokenAddressGrading] using
    (mme_basisZAllowedSubtensor_projection_certificate
      (coarseAddressObj K outer) (coarseAddressZBasis K outer)
      (addressWordSurvives m outer copy))
