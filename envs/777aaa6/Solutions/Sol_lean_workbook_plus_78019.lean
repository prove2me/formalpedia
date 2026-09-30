-- Prove2me | solution 1 for lean_workbook_plus_78019
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:34.398514+00:00
-- url     : https://prove2.me/submissions/d10bbc50-5463-4ee8-b022-a0afaac12cd5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (84 : ℝ) / 504 = 1 / 6 := by
  norm_num
