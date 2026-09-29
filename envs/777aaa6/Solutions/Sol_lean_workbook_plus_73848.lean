-- Prove2me | solution 1 for lean_workbook_plus_73848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:07.145354+00:00
-- url     : https://prove2.me/submissions/aa4ae1ce-a1ad-4911-9d1c-1687e3e732d9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : max x y = (|x - y| + x + y) / 2 := by
  intros
  grind
