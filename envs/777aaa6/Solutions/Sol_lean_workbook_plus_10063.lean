-- Prove2me | solution 1 for lean_workbook_plus_10063
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:03.777112+00:00
-- url     : https://prove2.me/submissions/af6aa48f-0984-4a54-8796-22ded0cee194

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (b - a) ^ 2 + (c - b) ^ 2 + (a - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  nlinarith only [sq_nonneg (a+b+c)]
