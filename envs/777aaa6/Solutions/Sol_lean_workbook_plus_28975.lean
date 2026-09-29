-- Prove2me | solution 1 for lean_workbook_plus_28975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:43.69765+00:00
-- url     : https://prove2.me/submissions/070fa8ce-6e0d-4e43-8826-a4fdd345e46d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 4*x + 2 = 0 ↔ x = 2 + Real.sqrt 2 ∨ x = 2 - Real.sqrt 2 := by
  intros
  grind
