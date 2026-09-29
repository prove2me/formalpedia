-- Prove2me | solution 1 for lean_workbook_plus_11976
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:03.307775+00:00
-- url     : https://prove2.me/submissions/3b41b255-c56d-470e-a0a3-d34ce4ab715f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (A B C D : ℝ) : (A - C) ^ 2 + (B - D) ^ 2 + (A - D) ^ 2 + (B - C) ^ 2 ≥ (A - B) ^ 2 + (C - D) ^ 2 := by
  nlinarith only [sq_nonneg (A+B-C-D)]
