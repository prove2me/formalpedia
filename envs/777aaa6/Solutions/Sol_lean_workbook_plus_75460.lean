-- Prove2me | solution 1 for lean_workbook_plus_75460
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:24.033933+00:00
-- url     : https://prove2.me/submissions/d38ea44e-05eb-4c0f-8768-c44bd0cb0548

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 239 ^ 30 ≡ 0 [ZMOD 239] := by
  decide
