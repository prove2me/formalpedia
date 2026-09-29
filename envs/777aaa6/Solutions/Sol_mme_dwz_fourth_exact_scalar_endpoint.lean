-- Prove2me | solution 1 for mme_dwz_fourth_exact_scalar_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:48:46.644016+00:00
-- url     : https://prove2.me/submissions/a5823a97-8a0a-4ffc-a6f1-1a676fc15adf

import Theorems.Thm_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
import Theorems.Thm_mme_dwz_fourth_terminal_log_margin
import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data
import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data

open MME MME.DWZFourthScalar
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

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

namespace MME.DWZFourthScalar

/- The recurrence checker and the terminal exponential comparison are kept in
   separate files so that the large finite computation is independent of the
   real-analysis wrapper.  This theorem is their exact interface. -/
private theorem exact_scalar_ledger_exceeds_2401_01 :
    (240101 / 100 : ℝ) <
      Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) := by
  apply fourth_value_exceeds_2401_01_of_natural_rate_floor
  exact_mod_cast
    MME.DWZFourthScalarLedger.exactRationalRecurrenceCertificate.2

end MME.DWZFourthScalar

theorem solution :
    (240101 / 100 : ℝ) <
      Real.exp (MME.DWZFourthScalarLedger.finalRateFloor : ℝ) :=
  exact_scalar_ledger_exceeds_2401_01
