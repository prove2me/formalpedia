-- Prove2me | solution 1 for lean_workbook_plus_46940
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:48:08.441907+00:00
-- url     : https://prove2.me/submissions/6ae893d9-b4ef-496e-9510-5bb8d547a909

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  Nat.gcd 180 594 = 18 := by
  simp
