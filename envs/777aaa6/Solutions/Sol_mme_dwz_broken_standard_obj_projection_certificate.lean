-- Prove2me | solution 1 for mme_dwz_broken_standard_obj_projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:21:04.738216+00:00
-- url     : https://prove2.me/submissions/02a12104-a21e-4781-a1d0-60f2c6c4cb3f

import Definitions.Def_mme_dwz_broken_standard_obj
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate

open MME Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)))) :
    TensorObj.Restrict
        (dwzBrokenStandardObj K m copy)
        (dwzTable2StandardObj K m) ∧
      (dwzBrokenStandardGrading K m copy).classOf 0 0 = ⊤ ∧
      (dwzBrokenStandardGrading K m copy).classOf 1 0 = ⊤ ∧
      (dwzBrokenStandardGrading K m copy).classOf 2 0 =
        Submodule.span K
          (dwzTable2StandardZBasis K m ''
            {W | groupedUsefulBlock m W ∈ copy.nonholes}) := by
  classical
  simpa [dwzBrokenStandardObj, dwzBrokenStandardGrading,
    TensorObj.basisZAllowedSubtensor, groupedWordSurvives] using
    (mme_basisZAllowedSubtensor_projection_certificate
      (dwzTable2StandardObj K m)
      (dwzTable2StandardZBasis K m)
      (groupedWordSurvives m copy))
