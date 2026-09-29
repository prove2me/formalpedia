-- Prove2me | solution 1 for lean_workbook_plus_28664
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:08.252751+00:00
-- url     : https://prove2.me/submissions/e34e7b40-ad2f-4729-b0a2-da338c74f413

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ)
  (h₀ : a = 1 / 2)
  (r : ℝ)
  (h₁ : r = 1 / 4) :
  a / (1 - r) = 2 / 3 := by
  intros
  grind
