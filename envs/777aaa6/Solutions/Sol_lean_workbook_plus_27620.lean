-- Prove2me | solution 1 for lean_workbook_plus_27620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:33.444089+00:00
-- url     : https://prove2.me/submissions/6fef2b90-7427-4922-a70a-7fa79be29f0b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 147 - 1 ≡ 0 [ZMOD 343] := by
  decide
