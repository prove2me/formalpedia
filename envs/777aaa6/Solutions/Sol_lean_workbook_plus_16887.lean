-- Prove2me | solution 1 for lean_workbook_plus_16887
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:55.790507+00:00
-- url     : https://prove2.me/submissions/b0498fc8-86cc-45dc-8ba0-09ae719cae2d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) :  (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 ↔ a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  intros
  grind
