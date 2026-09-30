-- Prove2me | solution 1 for lean_workbook_plus_78964
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:12.312156+00:00
-- url     : https://prove2.me/submissions/1120b746-78af-49f8-9333-ffd4cdad233d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : Nat.choose 5 3 = 10 := by
  decide
