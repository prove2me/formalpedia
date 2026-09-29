-- Prove2me | Theorems.Thm_mme_dwz_fourth_elementary_MM_six_endpoints
-- name    : mme_dwz_fourth_elementary_MM_six_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:31:32.065223+00:00
-- url     : https://prove2.me/theorems/0fbd0566-5b7e-4ff3-99d3-768788b9ad7b
-- title:
--   The 120 elementary matrix-multiplication six-region endpoints
-- statement:
--   At the mission exponent 790643 / 1000000, every elementary boundary row in the exact q=5 fourth-power scalar ledger lies below the tau-value of its explicit matrix-multiplication block. The finite classification and all log inequalities are checked exactly. Thus the only tensor-specific input for these 24 rows is their exact MMObj restriction; no real-valued endpoint premise remains.
--
--   Strongest exact-MM specialization: all 39 atomic, square-boundary, and fourth-boundary rows are fully discharged. The one remaining premise contains exactly 120 central/coupled square rows.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_elementary_MM_six_endpoints_data
import Theorems.Thm_mme_dwz_fourth_public_ordinary_181_reduction
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_stothers_elementary_fourth_constituent_MM_restrict
import Theorems.Thm_mme_stothers_cwFourth_cyclic_block_iso
import Theorems.Thm_mme_stothers_cwFourth_swapped_block_iso
import Theorems.Thm_mme_CW_block_is_MM_at_110
import Theorems.Thm_mme_CW_block_is_MM_at_101
import Theorems.Thm_mme_CW_block_is_MM_at_011
import Theorems.Thm_mme_CW_block_is_MM_at_200
import Theorems.Thm_mme_CW_block_is_MM_at_020
import Theorems.Thm_mme_CW_block_is_MM_at_002
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks

open MME MME.DWZFourthElementaryMM
open MME
open MME.DWZFourthTensorLedger
open MME.DWZFourthSixFinalSplit
open MME.DWZFourthPublicOrdinary181
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_elementary_MM_six_endpoints :
    ∀ {K : Type u} [Field K] (hcentral : CentralSquarePublicComplementSixEndpoints (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))),
    PublicComplementSixEndpoints
      (tensorAt (MME.DWZFourthPrescribedZ181.canonicalQ5Components K))
      (790643 / 1000000 : Real) := by sorry
