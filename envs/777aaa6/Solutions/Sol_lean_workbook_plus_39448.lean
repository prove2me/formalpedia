-- Prove2me | solution 1 for lean_workbook_plus_39448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:11.91417+00:00
-- url     : https://prove2.me/submissions/e618d621-cc29-4415-85fd-edbeeace7f72

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x y : ℝ) (h₁ : x = a - b) (h₂ : y = b - c) : (a - b) * (b - c) * (c - a) = -x * y * (x + y) := by
  intros
  grind
