-- Prove2me | solution 1 for lean_workbook_plus_22572
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:50.083026+00:00
-- url     : https://prove2.me/submissions/5452b38e-54a4-40a7-9fd7-b4528076163e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (v : ℝ)
  (h₀ : v = 3 * 1.5 - 1.5) :
  v = 3 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
