-- Prove2me | Theorems.Thm_mme_dwz_fourth_oneHot_40_integration_splice
-- name    : mme_dwz_fourth_oneHot_40_integration_splice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:44:38.824497+00:00
-- url     : https://prove2.me/theorems/f5e3a04b-666f-43e7-bb53-a4429b171b0c
-- title:
--   Splicing the one-hot endpoints into the 181-node integration
-- statement:
--   This module removes the two interface mismatches left after the generic one-hot endpoint lift. First, it proves that the lift's normalized profile is literally the profile fixed by the 181-node integration on every selected row. Second, it packages an actual basis of each component Z-space with the constant active grade. Thus the existing all-180 ordinary endpoint bundle supplies exact prescribed-Z endpoints, at the integration's exact profiles and rates, on all forty one-hot rows.
--
--   Direct exact-rate consumer of the existing ordinary endpoint bundle. The conclusion already uses ComponentBasisGradeData and componentZProfile, i.e. precisely the component-level data expected by the 181-node prescribed-Z integration.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_oneHot_40_integration_splice_data
import Theorems.Thm_mme_dwz_fourth_prescribedZ_181_integration
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
import Theorems.Thm_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy

open MME MME.DWZFourthPrescribedZ181 MME.DWZFourthPrescribedZ181.OneHotSplice
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_oneHot_40_integration_splice :
    (∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
      componentZProfile i = normalizedZProfile i) ∧
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
      ∀ (i : Fin 180),
        hasOneHotLedgerZProfile (componentSpecAt i) = true →
          HasPrescribedZSixRestrictionValueAtLeast
            (tensorAt i.castSucc)
            ((constantComponentData tensorAt).basis i)
            ((constantComponentData tensorAt).grade i)
            (componentZProfile i) tau
            (Real.exp
              (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ))) := by sorry
