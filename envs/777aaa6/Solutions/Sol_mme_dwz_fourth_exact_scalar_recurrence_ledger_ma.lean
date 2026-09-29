-- Prove2me | solution 1 for mme_dwz_fourth_exact_scalar_recurrence_ledger_ma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T18:14:44.046991+00:00
-- url     : https://prove2.me/submissions/44977ad8-9184-404e-9368-69c79d05c0a5

import Definitions.Def_mme_dwz_fourth_exact_scalar_recurrence_ledger_ma_data

open MME.DWZFourthScalarLedger
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem exactRationalRecurrenceCertificate :
    checkLedger = true /\ naturalRateFloor <= finalRateFloor := by
  decide +kernel

private theorem exactRationalRecurrenceCertificateReal :
    (naturalRateFloor : Real) <= (finalRateFloor : Real) := by
  exact_mod_cast exactRationalRecurrenceCertificate.2

theorem solution :
    (checkLedger = true /\ naturalRateFloor <= finalRateFloor) ∧
    ((naturalRateFloor : Real) <= (finalRateFloor : Real)) :=
  ⟨exactRationalRecurrenceCertificate, exactRationalRecurrenceCertificateReal⟩
