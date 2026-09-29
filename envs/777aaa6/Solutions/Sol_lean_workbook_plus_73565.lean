-- Prove2me | solution 1 for lean_workbook_plus_73565
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:20:21.906824+00:00
-- url     : https://prove2.me/submissions/8f699bd8-f88c-411d-a856-549005477456

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h₁ : x * y = 3 / 2) (h₂ : 0 ≤ x) (h₃ : 0 ≤ y) : 6 ≤ 10 * x + 3 * y / 5 := by
  by_contra hn
  have hp := mul_pos (show 0 < 6-(10*x+3*y/5) by linarith) (show 0 < 6+(10*x+3*y/5) by linarith)
  nlinarith [sq_nonneg (10*x-3*y/5)]
