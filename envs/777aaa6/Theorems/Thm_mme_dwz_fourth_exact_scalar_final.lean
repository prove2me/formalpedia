-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_scalar_final
-- name    : mme_dwz_fourth_exact_scalar_final
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T08:25:53.0857+00:00
-- url     : https://prove2.me/theorems/74ec31e8-64dc-4c5e-a293-3dd7b738e941
-- title:
--   The complete exact scalar certificate of the fourth-power construction
-- statement:
--   stated in Lean as
--
--   ```lean
--   MME.DWZFourthLogScaleTable.entries.all
--         MME.DWZFourthLogScaleTable.entryValid = true ∧
--       MME.DWZFourthRetainedEntropy.checkRetainedEntropy = true ∧
--       MME.DWZFourthScalarLedger.checkLedger = true ∧
--       (∀ i : Fin MME.DWZFourthLogScaleTable.entries.size,
--         (MME.autoScaledLogLower
--               (MME.DWZFourthLogScaleTable.argument i)
--               (MME.DWZFourthLogScaleTable.scale i) 6 : ℝ) ≤
--             Real.log (MME.DWZFourthLogScaleTable.argument i : ℝ) ∧
--           Real.log (MME.DWZFourthLogScaleTable.argument i : ℝ) ≤
--             (MME.autoScaledLogUpper
--               (MME.DWZFourthLogScaleTable.argument i)
--               (MME.DWZFourthLogScaleTable.scale i) 6 : ℝ)) ∧
--       (∀ i : Fin MME.DWZFourthRetainedEntropy.entropyRecords.size,
--         ((MME.DWZFourthRetainedEntropy.entropyRecords[i]).lowerFloor : ℝ) ≤
--             MME.DWZFourthExactScalarCertificate.entropyActual
--               (MME.DWZFourthRetainedEntropy.entropyRecords[i]).cells ∧
--           MME.DWZFourthExactScalarCertificate.entropyActual
--               (MME.DWZFourthRetainedEntropy.entropyRecords[i]).cells ≤
--             ((MME.DWZFourthRetainedEntropy.entropyRecords[i]).upperCeiling : ℝ)) ∧
--       (∀ i : Fin MME.DWZFourthRetainedEntropy.obligations.size,
--         ∃ actual,
--           MME.DWZFourthExactScalarCertificate.termsActual
--               (MME.DWZFourthRetainedEntropy.obligations[i]).terms = some actual ∧
--             ((MME.DWZFourthRetainedEntropy.obligations[i]).retainedFloor : ℝ) ≤
--               ((MME.DWZFourthRetainedEntropy.obligations[i]).constant : ℝ) + actual) ∧
--       (MME.DWZFourthScalarLedger.naturalRateFloor : ℝ) ≤
--         (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) ∧
--       (240101 / 100 : ℝ) <
--         Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ)
--   ```
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Theorems.Thm_mme_dwz_fourth_exact_scalar_certificate
import Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin
import Definitions.Def_mme_dwz_fourth_exact_scalar_certificate_data
import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data
import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data

open MME
open scoped Classical

set_option autoImplicit false

theorem mme_dwz_fourth_exact_scalar_final :
    MME.DWZFourthLogScaleTable.entries.all
        MME.DWZFourthLogScaleTable.entryValid = true ∧
      MME.DWZFourthRetainedEntropy.checkRetainedEntropy = true ∧
      MME.DWZFourthScalarLedger.checkLedger = true ∧
      (∀ i : Fin MME.DWZFourthLogScaleTable.entries.size,
        (MME.autoScaledLogLower
              (MME.DWZFourthLogScaleTable.argument i)
              (MME.DWZFourthLogScaleTable.scale i) 6 : ℝ) ≤
            Real.log (MME.DWZFourthLogScaleTable.argument i : ℝ) ∧
          Real.log (MME.DWZFourthLogScaleTable.argument i : ℝ) ≤
            (MME.autoScaledLogUpper
              (MME.DWZFourthLogScaleTable.argument i)
              (MME.DWZFourthLogScaleTable.scale i) 6 : ℝ)) ∧
      (∀ i : Fin MME.DWZFourthRetainedEntropy.entropyRecords.size,
        ((MME.DWZFourthRetainedEntropy.entropyRecords[i]).lowerFloor : ℝ) ≤
            MME.DWZFourthExactScalarCertificate.entropyActual
              (MME.DWZFourthRetainedEntropy.entropyRecords[i]).cells ∧
          MME.DWZFourthExactScalarCertificate.entropyActual
              (MME.DWZFourthRetainedEntropy.entropyRecords[i]).cells ≤
            ((MME.DWZFourthRetainedEntropy.entropyRecords[i]).upperCeiling : ℝ)) ∧
      (∀ i : Fin MME.DWZFourthRetainedEntropy.obligations.size,
        ∃ actual,
          MME.DWZFourthExactScalarCertificate.termsActual
              (MME.DWZFourthRetainedEntropy.obligations[i]).terms = some actual ∧
            ((MME.DWZFourthRetainedEntropy.obligations[i]).retainedFloor : ℝ) ≤
              ((MME.DWZFourthRetainedEntropy.obligations[i]).constant : ℝ) + actual) ∧
      (MME.DWZFourthScalarLedger.naturalRateFloor : ℝ) ≤
        (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) ∧
      (240101 / 100 : ℝ) <
        Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) := by sorry
