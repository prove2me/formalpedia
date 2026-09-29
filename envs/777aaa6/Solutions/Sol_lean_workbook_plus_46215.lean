-- Prove2me | solution 1 for lean_workbook_plus_46215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:34.818145+00:00
-- url     : https://prove2.me/submissions/fb3480f9-2c37-4c7d-a2f7-8f96bbbba094

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ)
  (h₀ : x * y * (x + y) = 30)
  (h₁ : x * y + (30 / (x * y)) = 11) :
  x + y = (30 / (x * y)) := by
  intros
  grind
