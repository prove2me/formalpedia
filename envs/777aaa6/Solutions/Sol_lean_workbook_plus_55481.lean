-- Prove2me | solution 1 for lean_workbook_plus_55481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:05.65896+00:00
-- url     : https://prove2.me/submissions/5e22050a-c841-49c6-8365-1788a70e0eed

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x^2 - 12*x + 35 = 0 ↔ x = 5 ∨ x = 7 := by
  intros
  grind
