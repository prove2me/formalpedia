-- Prove2me | solution 1 for lean_workbook_plus_42055
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:37.595907+00:00
-- url     : https://prove2.me/submissions/bcf8324c-d157-46c4-b8a8-4fec11fb44d6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (hx: a > b ∧ b > c) : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) > 0 := by
  rcases hx with ⟨hab,hbc⟩
  have hp := mul_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)) (show 0<a-c by linarith)
  nlinarith
