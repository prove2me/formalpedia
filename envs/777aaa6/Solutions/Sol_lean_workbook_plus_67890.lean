-- Prove2me | solution 1 for lean_workbook_plus_67890
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:55.29641+00:00
-- url     : https://prove2.me/submissions/c186bc3c-72f9-4e10-b013-972d5427b169

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (h₁ : b - a = 1 ∨ b - a = 2) : |a - b| ≤ 2 := by
  intros
  grind
