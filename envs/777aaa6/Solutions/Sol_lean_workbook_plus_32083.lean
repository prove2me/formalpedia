-- Prove2me | solution 1 for lean_workbook_plus_32083
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:01.589639+00:00
-- url     : https://prove2.me/submissions/2960f222-6e30-4ab7-bf88-b0644589adda

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  Nat.choose 5 3 = 10 := by
  decide
