-- Prove2me | solution 1 for lean_workbook_plus_19594
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:00.76705+00:00
-- url     : https://prove2.me/submissions/cb524fc7-95c8-45a8-bdfa-41514a12a520

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) ≥ ((a + b) * (b + c) * (c + a) - 4 * a * b * c) ^ 2 := by
  intro a b c
  nlinarith only [sq_nonneg ((a-b)*(a-c)*(b-c))]
