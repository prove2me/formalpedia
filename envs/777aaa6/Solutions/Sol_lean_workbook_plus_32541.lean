-- Prove2me | solution 1 for lean_workbook_plus_32541
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:37.751805+00:00
-- url     : https://prove2.me/submissions/76d2f80d-75ef-455d-96a1-4fcd5dc41f6d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^9 + 2^7 + 1 ∣ 2^32 + 1 := by
  norm_num
