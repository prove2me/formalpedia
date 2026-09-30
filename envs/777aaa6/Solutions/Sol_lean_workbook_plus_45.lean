-- Prove2me | solution 1 for lean_workbook_plus_45
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:42.428287+00:00
-- url     : https://prove2.me/submissions/da4e791b-06bd-4df0-b6dc-53eb70a4bf63

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (5^(2*1) ≡ 25 [MOD 100]) := by
  decide
