-- Prove2me | solution 1 for lean_workbook_plus_26090
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:16.722046+00:00
-- url     : https://prove2.me/submissions/9d68c05e-bc8f-4621-94a7-4f2891f00ffd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : ∀ x y : ℤ, x*y = y*x := by
  intros; nlinarith [sq_nonneg (by assumption : _), sq_nonneg 1]
