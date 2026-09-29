-- Prove2me | Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
-- name    : mme_dwz_fourth_oneHot_40_prescribedZ_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:35:55.88724+00:00
-- url     : https://prove2.me/theorems/09f0cbd5-6756-45ff-8797-d0914e621517
-- title:
--   The 40 one-hot prescribed-Z ledger endpoints
-- statement:
--   This file turns the computational one-hot census into a tensor-level endpoint theorem. Atomic sentinel profiles are normalized to [1, 0]; every other profile is the literal generated ledger profile. On each of the forty rows, the active grade is computed from that normalized list. Consequently an ordinary six-symmetric endpoint for a constant-grade realization lifts to the required prescribed-Z endpoint at exactly the same value.
--
--   Exact-rate specialization for the existing 181-node ordinary endpoint bundle. This is the direct splice into the fourth-ledger proof: no endpoint value or profile assumption remains on any of the forty selected rows.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints_data
import Theorems.Thm_mme_dwz_fourth_public_component_coverage
import Theorems.Thm_mme_HasPrescribedZSix_of_constant_grade_oneHot
import Theorems.Thm_mme_dwz_fourth_six_value_final_node_split

open MME MME.DWZFourthTensorLedger MME.DWZFourthTensorLedger.OneHotEndpoints
open MME Module
open MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_oneHot_40_prescribedZ_endpoints :
    ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (ι : Fin 180 → Type u) (basis : (i : Fin 180) → Basis (ι i) K ((tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i)).V 2)) (grade : (i : Fin 180) → ι i → Fin (componentSpecAt i).address.zWidth) (tau : ℝ) (hgrade : ConstantOnOneHotRows (K := K) ι grade) (hordinary : DWZFourthSixFinalSplit.ProperSixEndpointsPointwise tensorAt tau),
    ∀ (i : Fin 180),
      hasOneHotLedgerZProfile (componentSpecAt i) = true →
        HasPrescribedZSixRestrictionValueAtLeast
          (tensorAt (DWZFourthSixFinalSplit.properLedgerIndex i))
          (basis i) (grade i) (normalizedZProfile i) tau
          (Real.exp
            (DWZFourthSixFinalSplit.properLedgerRate i : ℝ)) := by sorry
