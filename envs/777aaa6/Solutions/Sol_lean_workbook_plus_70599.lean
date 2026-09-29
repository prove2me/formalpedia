-- Prove2me | solution 1 for lean_workbook_plus_70599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:29.875683+00:00
-- url     : https://prove2.me/submissions/9a402d87-7bd5-4501-830c-02ac7aeb41f7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^3 + 1 / (3 * Real.sqrt 3) + 1 / (3 * Real.sqrt 3) ≥ x → x * (1 - x^2) ≤ 2 / (3 * Real.sqrt 3) := by
  intros
  grind
