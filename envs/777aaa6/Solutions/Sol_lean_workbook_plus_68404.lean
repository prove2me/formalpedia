-- Prove2me | solution 1 for lean_workbook_plus_68404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:58.301911+00:00
-- url     : https://prove2.me/submissions/5cbada7e-239f-447f-a7d8-98104eec5ad9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h₁ : x + y = 3) (h₂ : x * y = 2) : x^5 + y^5 = 33 := by
  intros
  grind
