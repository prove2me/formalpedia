-- Prove2me | solution 1 for lean_workbook_plus_4188
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:40.326729+00:00
-- url     : https://prove2.me/submissions/88c5d204-57d3-4030-94d9-e60a20645d4e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (h₁ : a + b = 50) (h₂ : a * b = 25) : 1 / a + 1 / b = 2 := by
  intros
  grind
