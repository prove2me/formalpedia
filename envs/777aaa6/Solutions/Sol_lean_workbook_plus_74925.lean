-- Prove2me | solution 1 for lean_workbook_plus_74925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:28.450805+00:00
-- url     : https://prove2.me/submissions/77a64c37-8549-4453-9eef-1beeaf33200b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q r s : ℝ) : ((p - r) / (q - s)) = -1 → |p - r| = |q - s| := by
  intros
  grind
