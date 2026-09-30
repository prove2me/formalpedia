-- Prove2me | solution 1 for lean_workbook_plus_10976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:25.9033+00:00
-- url     : https://prove2.me/submissions/af41d5d5-bedb-44ff-b0f6-4bd928e438cf

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 19 ^ 128 ≡ -1 [ZMOD 257] := by
  decide
