-- Prove2me | solution 1 for lean_workbook_plus_7134
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:52.922362+00:00
-- url     : https://prove2.me/submissions/2aa5fe7e-e5be-4d8f-b2d2-7f0a9d46196f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : 2 * (1 + x^2 * y^2) / (x * y) = 2 * (1 / (x * y) + x * y) := by
  intros
  grind
