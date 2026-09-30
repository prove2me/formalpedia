-- Prove2me | solution 1 for lean_workbook_plus_3345
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:59.412501+00:00
-- url     : https://prove2.me/submissions/fe88cb89-ab21-4525-bb9b-a102c5135c9d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (5:ℝ)^51 ≥ 2^118 := by
  norm_num
