-- Prove2me | solution 1 for lean_workbook_plus_44499
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:49.032493+00:00
-- url     : https://prove2.me/submissions/b4d1b655-ee67-4c03-a3cf-b6c182fc2fb2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 99 ≡ 8 [MOD 10] := by
  decide
