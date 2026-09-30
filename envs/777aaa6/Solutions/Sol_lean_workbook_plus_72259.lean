-- Prove2me | solution 1 for lean_workbook_plus_72259
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:44.228364+00:00
-- url     : https://prove2.me/submissions/8b075e67-611e-46b4-9c42-0f2ba4870606

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2022 ≡ 6 [ZMOD 96] := by
  decide
