-- Prove2me | Definitions.Def_mme_dwz_fourth_oneHot_40_integration_splice_data
-- name    : mme_dwz_fourth_oneHot_40_integration_splice_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:44:15.263007+00:00
-- url     : https://prove2.me/theorems/38d2466c-048f-4957-9274-75c07d817c57
-- title:
--   Splicing the one-hot endpoints into the 181-node integration
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_oneHot_40_integration_splice, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_prescribedZ_181_integration_data
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_integration
import Definitions.Def_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
import Definitions.Def_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy_data
import Theorems.Thm_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy

open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open scoped Classical

universe u

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthPrescribedZ181.OneHotSplice

/-- An actual basis/grade package for every proper component.  The basis is
chosen on the literal Z-space `((tensorAt i.castSucc).V 2)` and every one-hot
row is assigned its uniquely active grade.  Values on non-one-hot rows are
harmless here and can later be replaced when the other endpoint families are
spliced in. -/
noncomputable def constantComponentData
    {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) :
    ComponentBasisGradeData tensorAt where
  ι := componentBasisIndex tensorAt
  basis := componentBasis tensorAt
  grade i := fun _ ↦ activeGrade i

end MME.DWZFourthPrescribedZ181.OneHotSplice


