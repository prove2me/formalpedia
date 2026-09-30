-- Prove2me | solution 1 for lean_workbook_plus_15188
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:26.166608+00:00
-- url     : https://prove2.me/submissions/1147b296-2bc9-490b-864c-923fe12fd9a6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 4^31 * 4 ≡ 4^32 [ZMOD 12] := by
  norm_num
