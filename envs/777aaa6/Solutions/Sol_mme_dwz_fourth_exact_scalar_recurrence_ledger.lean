-- Prove2me | solution 1 for mme_dwz_fourth_exact_scalar_recurrence_ledger
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:58:42.367323+00:00
-- url     : https://prove2.me/submissions/a4eb7200-100b-4c8d-80d0-234ac7121897

import Definitions.Def_mme_dwz_fourth_exact_scalar_ledger_data

open MME.DWZFourthScalarLedger

set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution :
    checkLedger = true /\ naturalRateFloor <= finalRateFloor := by
  decide +kernel
