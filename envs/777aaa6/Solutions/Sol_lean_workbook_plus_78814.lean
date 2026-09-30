-- Prove2me | solution 1 for lean_workbook_plus_78814
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:53.201456+00:00
-- url     : https://prove2.me/submissions/4f9668b1-3e7b-4bb6-9ce0-84c8b12b2cde

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem solution :
    Finset.card (Finset.filter (fun x => 6 ∣ x) (Finset.Icc 1 999)) -
    Finset.card (Finset.filter (fun x => 6 ∣ x) (Finset.Icc 1 99)) = 150 := by
  decide
