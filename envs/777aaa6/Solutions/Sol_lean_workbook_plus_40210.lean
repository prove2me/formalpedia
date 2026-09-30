-- Prove2me | solution 1 for lean_workbook_plus_40210
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:15.780618+00:00
-- url     : https://prove2.me/submissions/e91fc8a2-deb5-4ca5-8a52-b5d05df9f99e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3^(2^6) + 3 ≡ 0 [ZMOD 19] := by
  decide
