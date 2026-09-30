-- Prove2me | solution 1 for lean_workbook_plus_27960
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:58.927587+00:00
-- url     : https://prove2.me/submissions/f76659b3-6f67-478f-bf85-1fc7292c0a84

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 4 ^ 237 ≡ 4 [ZMOD 12] := by
  decide
