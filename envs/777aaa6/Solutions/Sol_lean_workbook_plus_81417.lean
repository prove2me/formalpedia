-- Prove2me | solution 1 for lean_workbook_plus_81417
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:08.181117+00:00
-- url     : https://prove2.me/submissions/6544e1f8-8fbb-4025-983d-fca67b61e550

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : Nat.choose 10 3 = 120 := by
  decide
