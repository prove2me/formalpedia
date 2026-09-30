-- Prove2me | solution 1 for lean_workbook_plus_1080
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:17.397596+00:00
-- url     : https://prove2.me/submissions/ebbe3c26-bd36-49d1-9c07-f854d3976b75

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : Nat.choose 9 4 = 126 := by
  decide
