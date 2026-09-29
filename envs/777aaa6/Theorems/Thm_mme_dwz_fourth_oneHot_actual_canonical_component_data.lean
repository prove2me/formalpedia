-- Prove2me | Theorems.Thm_mme_dwz_fourth_oneHot_actual_canonical_component_data
-- name    : mme_dwz_fourth_oneHot_actual_canonical_component_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:46:31.168489+00:00
-- url     : https://prove2.me/theorems/94e38042-ab98-4c2f-b0f2-ffcae4110feb
-- title:
--   Canonical component data for the one-hot fourth-power rows
-- statement:
--   Unlike the purely constant temporary package, this file chooses the literal canonical restricted-fiber basis and first-factor fine grading on every square and fourth component. These are the same data used by the recursive CW decompositions on the remaining rows. Extremality of the forty one-hot Z blocks proves that this globally useful grading is constant exactly where the reverse one-hot restriction theorem needs it.
--
--   The direct ordinary-to-prescribed lift, now using one coherent canonical component family rather than a row-local constant choice.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_oneHot_actual_canonical_component_data_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_integration_splice

open MME MME.DWZFourthPrescribedZ181 MME.DWZFourthPrescribedZ181.OneHotActualCanonical
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open scoped Classical

universe u v

set_option autoImplicit false

theorem mme_dwz_fourth_oneHot_actual_canonical_component_data :
    ∀ {K : Type u} [Field K] (hordinary : MME.DWZFourthSixFinalSplit.ProperSixEndpointsPointwise (tensorAt (canonicalQ5Components K)) (790643 / 1000000 : ℝ)),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (canonicalQ5Components K) i.castSucc)
          ((componentData K).basis i) ((componentData K).grade i)
          (componentZProfile i) (790643 / 1000000 : ℝ)
          (Real.exp
            (MME.DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by sorry
