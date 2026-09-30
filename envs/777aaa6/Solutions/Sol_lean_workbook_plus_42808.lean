-- Prove2me | solution 1 for lean_workbook_plus_42808
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:12:34.995492+00:00
-- url     : https://prove2.me/submissions/cda48b6f-fc69-4195-aa26-37a8040134ea

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) : 1 / 4 < x ↔ x > 1 / 4 := by
  norm_num
