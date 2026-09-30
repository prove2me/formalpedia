-- Prove2me | solution 1 for lean_workbook_plus_1521
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:04.349363+00:00
-- url     : https://prove2.me/submissions/ff523545-b251-48f4-a418-7ace44a800c6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 21 ^ 20 ≡ 1 [ZMOD 100] := by
  decide
