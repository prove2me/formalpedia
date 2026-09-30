-- Prove2me | solution 1 for lean_workbook_plus_51035
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:18.616933+00:00
-- url     : https://prove2.me/submissions/83489566-80da-4991-8140-1e0ec358df25

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 8 ^ 10 ≡ 1 [ZMOD 11] := by
  decide
