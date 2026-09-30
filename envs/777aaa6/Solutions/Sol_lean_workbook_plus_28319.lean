-- Prove2me | solution 1 for lean_workbook_plus_28319
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:53.982711+00:00
-- url     : https://prove2.me/submissions/2625fa20-6d54-48de-af70-339b1be63474

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : Nat.choose 8 3 = 56 := by
  decide
