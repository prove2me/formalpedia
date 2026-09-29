-- Prove2me | solution 1 for lean_workbook_plus_4979
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:18.745779+00:00
-- url     : https://prove2.me/submissions/49326d0a-6bde-4249-b34e-d0f089a09d5a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (r t : ℝ) (h₁ : r * t = 50) : t = 50 / r := by
  intros
  grind
