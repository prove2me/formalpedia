-- Prove2me | solution 1 for lean_workbook_plus_56292
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:00.948888+00:00
-- url     : https://prove2.me/submissions/01706809-349f-4094-b917-10aa4eb402d6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 15 ^ 18 ≡ 1 [ZMOD 19] := by
  decide
