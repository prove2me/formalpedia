-- Prove2me | solution 1 for lean_workbook_plus_41921
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:05.985689+00:00
-- url     : https://prove2.me/submissions/56393af2-5785-435e-a8f4-38e53c26a6ee

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 ^ 18 ≡ 1 [ZMOD 19] := by
  decide
