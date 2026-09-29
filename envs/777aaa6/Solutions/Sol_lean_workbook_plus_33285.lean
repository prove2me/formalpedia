-- Prove2me | solution 1 for lean_workbook_plus_33285
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:13.621607+00:00
-- url     : https://prove2.me/submissions/de70f448-48bc-4583-9800-f8873a227434

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0) :
  a / b + b / a = (a^2 + b^2) / (a * b) := by
  intros
  grind
