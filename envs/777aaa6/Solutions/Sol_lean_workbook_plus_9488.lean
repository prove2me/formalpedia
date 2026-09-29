-- Prove2me | solution 1 for lean_workbook_plus_9488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:46.970736+00:00
-- url     : https://prove2.me/submissions/4636bd64-21e7-49c5-8dd8-9882ed803eef

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p : ℝ) (hp_pos : 0 < p) (hp_lt_on_3 : p < 1/3) : -(p^2 / 6) + p^3 / 2 < 0 := by
  have hs : 0 < p^2 := sq_pos_of_pos hp_pos
  nlinarith [mul_pos hs (sub_pos.mpr hp_lt_on_3)]
