-- Prove2me | solution 1 for lean_workbook_plus_55038
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:50.120366+00:00
-- url     : https://prove2.me/submissions/4e26ae1b-1983-4d0b-9866-4c675f76743a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : 1 / (Real.sqrt n + Real.sqrt (n + 1)) = Real.sqrt (n + 1) - Real.sqrt n := by
  intros
  grind
