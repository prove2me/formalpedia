-- Prove2me | solution 1 for lean_workbook_plus_30281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:47.684382+00:00
-- url     : https://prove2.me/submissions/6c98f4ba-d8da-4377-b969-73b3acb53e65

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : a ≠ b)
  (h₂ : (b^2 - 2 * a * b) / (a^2 - 2 * a * b) = 117 / 165) :
  (b / a - 2) / (a / b - 2) = 117 / 165 := by
  clear h₁
  norm_num at *
  grind
