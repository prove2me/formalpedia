-- Prove2me | solution 1 for lean_workbook_plus_49775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:04.964046+00:00
-- url     : https://prove2.me/submissions/58948d66-20fd-4d71-a98a-6481f85e451a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) :
  a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1 ≥ 2 * a * b + 2 * b * c + 2 * c * a := by
  intros
  have h : (0 : ℝ) ≤ (a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1) - (2 * a * b + 2 * b * c + 2 * c * a) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1) - (2 * a * b + 2 * b * c + 2 * c * a) := by ring
  exact sub_nonneg.mp h
