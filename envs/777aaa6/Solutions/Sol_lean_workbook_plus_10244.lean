-- Prove2me | solution 1 for lean_workbook_plus_10244
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:20.448973+00:00
-- url     : https://prove2.me/submissions/d2a11380-3671-4cb9-bb71-59ddfcf4171d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx: x = 8^85): x > 5^100 ∧ x > 6^95 ∧ x > 7^90 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
