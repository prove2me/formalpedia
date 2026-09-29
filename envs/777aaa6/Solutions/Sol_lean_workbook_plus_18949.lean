-- Prove2me | solution 1 for lean_workbook_plus_18949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:03.232048+00:00
-- url     : https://prove2.me/submissions/56d2b4b5-c132-4806-912f-959c54308c5b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h₁ : a + b + c = 1) (h₂ : a^3 + b^3 + c^3 = 1) : (a * b + b * c + c * a)^3 = a^3 * b^3 + b^3 * c^3 + c^3 * a^3 := by
  intros
  grind
