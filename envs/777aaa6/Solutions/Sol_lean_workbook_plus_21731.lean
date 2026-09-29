-- Prove2me | solution 1 for lean_workbook_plus_21731
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:44.221979+00:00
-- url     : https://prove2.me/submissions/7c509103-aeb6-406d-bfa8-d41faf621537

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h1 : a ≠ b) (h2 : a ≠ -b) : (a + b) ^ 2 / 4 > a * b := by
  have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr h1)
  nlinarith
