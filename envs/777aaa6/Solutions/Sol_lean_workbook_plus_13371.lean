-- Prove2me | solution 1 for lean_workbook_plus_13371
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:28.296887+00:00
-- url     : https://prove2.me/submissions/93549acd-a5fd-4142-b969-5469df04cce8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (hab : a ≠ b) : (a + b) ^ 2 / 4 > a * b := by
  have h : (a - b)^2 > 0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  nlinarith
