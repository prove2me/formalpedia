-- Prove2me | solution 1 for lean_workbook_plus_52653
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:18.82719+00:00
-- url     : https://prove2.me/submissions/a0f9de0a-a961-4556-9271-02b19caaaaac

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) : -1 < (x - 1) * (y - 1) * (z - 1) ∧ (x - 1) * (y - 1) * (z - 1) < 0 := by
  have hxy : 0 < (1-x)*(1-y) := mul_pos (by linarith) (by linarith)
  have hxy1 : (1-x)*(1-y) < 1 := by nlinarith [mul_pos hx.1 (by linarith : 0 < 1-y)]
  have hp : 0 < ((1-x)*(1-y))*(1-z) := mul_pos hxy (by linarith)
  have hp1 : ((1-x)*(1-y))*(1-z) < 1 := by nlinarith [mul_pos hxy hz.1]
  constructor <;> nlinarith
