-- Prove2me | solution 1 for lean_workbook_plus_62586
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:38.178598+00:00
-- url     : https://prove2.me/submissions/e81d2548-a7cb-4889-94cc-d6061a6d6c85

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 10110 ≡ 6 [ZMOD 8] := by
  decide
