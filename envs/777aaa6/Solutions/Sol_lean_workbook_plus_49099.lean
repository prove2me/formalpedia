-- Prove2me | solution 1 for lean_workbook_plus_49099
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:02.172704+00:00
-- url     : https://prove2.me/submissions/b46fb0e3-050b-42d8-a04b-b045caf52ec8

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (7^2011) % 100 = 43 := by
  omega
