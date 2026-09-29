-- Prove2me | solution 1 for lean_workbook_plus_27829
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:01.77126+00:00
-- url     : https://prove2.me/submissions/5624394b-0bcf-4697-b8f8-56c9505531aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x ≠ y) (h₂ : x^3 - x = y^3 - y) : x^2 + y^2 + x*y = 1 := by
  intros
  grind
