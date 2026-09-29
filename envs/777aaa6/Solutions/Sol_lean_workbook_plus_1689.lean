-- Prove2me | solution 1 for lean_workbook_plus_1689
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:23.566378+00:00
-- url     : https://prove2.me/submissions/d754273d-413e-4c59-86e4-3a3927d6d97b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a^2 + b^2 + c^2 = 1 → (a - b)^2 + (b - c)^2 + (c - a)^2 ≤ 3 := by
  intro a b c h
  nlinarith [sq_nonneg (a+b+c)]
