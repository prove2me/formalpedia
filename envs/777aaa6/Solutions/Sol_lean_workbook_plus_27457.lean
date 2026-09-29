-- Prove2me | solution 1 for lean_workbook_plus_27457
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:40.645932+00:00
-- url     : https://prove2.me/submissions/417ea4cf-c7fd-4bee-be5d-8c6ab58dd32a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h : ∀ e : ℝ, e > 0 → x + e < y) : x ≤ y := by
  have hh := h 1 (by norm_num)
  linarith
