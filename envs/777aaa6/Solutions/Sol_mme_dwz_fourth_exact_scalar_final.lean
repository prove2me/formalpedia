-- Prove2me | solution 1 for mme_dwz_fourth_exact_scalar_final
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T08:26:00.84905+00:00
-- url     : https://prove2.me/submissions/7a9320c5-7e8e-4b76-9955-8901f8bed23c

import Theorems.Thm_mme_dwz_fourth_exact_scalar_certificate
import Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin
import Definitions.Def_mme_dwz_fourth_exact_scalar_certificate_data
import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data
import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data

open MME
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthLogScaleTable

theorem entries_all_valid : entries.all entryValid = true := by
  rw [Array.all_eq_true]
  intro i hi
  exact decide_eq_true (mme_dwz_fourth_exact_log_scale_table.1 ⟨i, hi⟩)

theorem interval_of_index (i : Fin entries.size) :
    (MME.autoScaledLogLower (argument i) (scale i) 6 : Real) <=
        Real.log (argument i : Real) ∧
      Real.log (argument i : Real) <=
        (MME.autoScaledLogUpper (argument i) (scale i) 6 : Real) :=
  mme_dwz_fourth_exact_log_scale_table.2 i

end MME.DWZFourthLogScaleTable
namespace MME.DWZFourthRetainedEntropy

theorem exactRetainedEntropyArithmetic :
    checkRetainedEntropy = true :=
  mme_dwz_fourth_exact_retained_entropy_arithmetic

end MME.DWZFourthRetainedEntropy
namespace MME.DWZFourthExactScalarCertificate
open MME
open MME.DWZFourthLogScaleTable
open MME.DWZFourthRetainedEntropy
open scoped Classical

theorem allRetainedEntropyRecordsSound :
    ∀ (i : Fin entropyRecords.size),
    ((entropyRecords[i]).lowerFloor : ℝ) ≤
        entropyActual (entropyRecords[i]).cells ∧
      entropyActual (entropyRecords[i]).cells ≤
        ((entropyRecords[i]).upperCeiling : ℝ) :=
  mme_dwz_fourth_exact_scalar_certificate.1

theorem allRetainedBranchesSound :
    ∀ (i : Fin obligations.size),
    ∃ actual, termsActual (obligations[i]).terms = some actual ∧
      ((obligations[i]).retainedFloor : ℝ) ≤
        ((obligations[i]).constant : ℝ) + actual :=
  mme_dwz_fourth_exact_scalar_certificate.2

end MME.DWZFourthExactScalarCertificate
namespace MME.DWZFourthScalarLedger
open scoped Classical

theorem exactRationalRecurrenceCertificate :
    checkLedger = true /\ naturalRateFloor <= finalRateFloor :=
  mme_dwz_fourth_exact_scalar_recurrence_ledger_ma.1

theorem exactRationalRecurrenceCertificateReal :
    (naturalRateFloor : Real) <= (finalRateFloor : Real) :=
  mme_dwz_fourth_exact_scalar_recurrence_ledger_ma.2

end MME.DWZFourthScalarLedger
namespace MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

theorem fourth_value_exceeds_2401_01_of_natural_rate_floor :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate :=
  mme_dwz_fourth_terminal_log_margin

end MME.DWZFourthScalar

namespace MME.DWZFourthExactScalarFinal

private theorem exact_scalar_certificate :
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
        Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) := by
  refine ⟨MME.DWZFourthLogScaleTable.entries_all_valid,
    MME.DWZFourthRetainedEntropy.exactRetainedEntropyArithmetic,
    MME.DWZFourthScalarLedger.exactRationalRecurrenceCertificate.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact MME.DWZFourthLogScaleTable.interval_of_index
  · exact MME.DWZFourthExactScalarCertificate.allRetainedEntropyRecordsSound
  · exact MME.DWZFourthExactScalarCertificate.allRetainedBranchesSound
  · exact MME.DWZFourthScalarLedger.exactRationalRecurrenceCertificateReal
  · apply MME.DWZFourthScalar.fourth_value_exceeds_2401_01_of_natural_rate_floor
    simpa [MME.DWZFourthScalar.naturalRateFloor,
      MME.DWZFourthScalarLedger.naturalRateFloor] using
        MME.DWZFourthScalarLedger.exactRationalRecurrenceCertificateReal

end MME.DWZFourthExactScalarFinal

open MME.DWZFourthExactScalarFinal in
theorem solution :
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
        Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) :=
  exact_scalar_certificate
