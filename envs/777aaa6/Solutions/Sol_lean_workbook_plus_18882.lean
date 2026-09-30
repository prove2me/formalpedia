-- Prove2me | solution 1 for lean_workbook_plus_18882
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:31.563496+00:00
-- url     : https://prove2.me/submissions/d79c428c-fd35-4eee-bb13-522048f68651

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (z : ℂ) : ‖z ^ 15‖ = ‖z‖ ^ 15 := by
  norm_num
