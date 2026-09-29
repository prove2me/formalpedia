-- Prove2me | Theorems.Thm_mme_dwz_fourth_six_value_final_node_split
-- name    : mme_dwz_fourth_six_value_final_node_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:01:10.528999+00:00
-- url     : https://prove2.me/theorems/ea80c2ee-bf5c-4243-805c-1c50369d635d
-- title:
--   Splitting the fourth-power ledger into proper rows and one global node
-- statement:
--   The first 180 component facts in this interface are ordinary HasSixSymmetricTauValueAtLeast endpoints. Prescribed-Z bases, grades, profiles, and their physical-length synchronization are not needed there. The only tensor-specific recursive operation left is the final global node. This is the direct consumer for independently proved square/fourth coarse-block values such as mme_dwz_fourth_coarse_block_value_of_pair_factor_values.
--
--   The statement is the conjunction of 2 facts about this stage of the fourth-power assembly:
--
--   (1) stated in Lean as
--
--   ```lean
--   ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpointwise : ProperSixEndpointsPointwise tensorAt tau),
--     ProperSixEndpoints tensorAt tau
--   ```
--
--   (2) stated in Lean as
--
--   ```lean
--   ∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hproper : ProperSixEndpoints tensorAt tau) (hglobal : FinalSixExtraction tensorAt tau),
--     HasSixSymmetricTauValueAtLeast
--       (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ)
--   ```
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_six_value_final_node_split_data
import Theorems.Thm_mme_dwz_fourth_scalar_ledger_induction_facade

open MME MME.DWZFourthSixFinalSplit
open MME
open MME.DWZFourthScalarLedger
open MME.DWZFourthScalarLedgerInduction
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_six_value_final_node_split :
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hpointwise : ProperSixEndpointsPointwise tensorAt tau),
      ProperSixEndpoints tensorAt tau) ∧
    (∀ {K : Type u} [Field K] (tensorAt : Fin 181 → TensorObj K 3) (tau : ℝ) (hproper : ProperSixEndpoints tensorAt tau) (hglobal : FinalSixExtraction tensorAt tau),
      HasSixSymmetricTauValueAtLeast
        (tensorAt ⟨180, by norm_num⟩) tau (240101 / 100 : ℝ)) := by sorry
