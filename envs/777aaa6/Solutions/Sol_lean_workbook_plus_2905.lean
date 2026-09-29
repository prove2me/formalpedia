-- Prove2me | solution 1 for lean_workbook_plus_2905
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:53.663314+00:00
-- url     : https://prove2.me/submissions/abda38db-a37a-4c07-95b4-d3d62974fdd5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (habc : a + b + c = 4 - d) : a * b + b * c + c * a ≥ 4 - d ^ 2 := by
  intros
  nlinarith
