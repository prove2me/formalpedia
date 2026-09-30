-- Prove2me | solution 1 for lean_workbook_plus_28101
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:05.292347+00:00
-- url     : https://prove2.me/submissions/1e75eac7-cb10-4881-b085-b0804e968485

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5 ^ 99 ≡ 0 [ZMOD 25] := by
  decide
