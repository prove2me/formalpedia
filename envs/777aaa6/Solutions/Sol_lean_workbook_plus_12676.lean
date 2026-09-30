-- Prove2me | solution 1 for lean_workbook_plus_12676
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:18.07013+00:00
-- url     : https://prove2.me/submissions/8bbf3941-b67c-4533-86f4-a4897b83f12b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 ^ 127 ≡ 3 [MOD 127] := by
  decide
