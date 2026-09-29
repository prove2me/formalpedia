-- Prove2me | solution 1 for lean_workbook_plus_18355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:27.472896+00:00
-- url     : https://prove2.me/submissions/3280a03b-7022-4ff9-afed-c58d38ad49d5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (f g : ℝ → ℝ) (hf : f x = 1 / x) (hg : g x = -1 / x) : f x + g x = 0 := by
  intros
  grind
