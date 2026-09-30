-- Prove2me | solution 1 for lean_workbook_plus_67713
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:05.258472+00:00
-- url     : https://prove2.me/submissions/21eec30e-69fa-48f3-a3be-e3b38d48de3f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 32 ≡ -1 [ZMOD 641] := by
  decide
