-- Prove2me | solution 1 for lean_workbook_plus_17783
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:43.533096+00:00
-- url     : https://prove2.me/submissions/f8247d46-a6a0-4070-a58e-93055c3fcdde

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : x = 1) : 7 = x^3 + 3 * x * y ↔ y = 2 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
