-- Prove2me | solution 1 for lean_workbook_plus_6281
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:14.886651+00:00
-- url     : https://prove2.me/submissions/814ead21-7462-4386-a476-47ae2d566028

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : Nat.choose 8 6 = 28 := by
  decide
