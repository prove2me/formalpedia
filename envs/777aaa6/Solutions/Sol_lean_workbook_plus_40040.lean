-- Prove2me | solution 1 for lean_workbook_plus_40040
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:11:09.755315+00:00
-- url     : https://prove2.me/submissions/ea6e9cf3-52f0-45ad-9c99-351d3afbd22d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) : (a + c) ^ 2 ≥ a * b + b * c + c * a := by
  by_cases hsum : 0 ≤ a + c
  · have h := mul_nonneg (show 0 ≤ a - b by linarith) hsum
    nlinarith [h, sq_nonneg c]
  · have h := mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ -(a + c) by linarith)
    nlinarith [h, sq_nonneg a]
