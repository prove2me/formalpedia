-- Prove2me | solution 1 for lean_workbook_plus_74620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:59.514131+00:00
-- url     : https://prove2.me/submissions/0f276e70-6996-4569-b8f8-e92de7a7344b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 * 3 * 5 * 7 > 11 ^ 2 := by
  norm_num
