-- Prove2me | solution 1 for lean_workbook_plus_56543
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:19.903556+00:00
-- url     : https://prove2.me/submissions/c4223bac-5e8f-406b-a1b3-297beb1e84cf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  ∀ x y z : ℝ,
    2 * z = (2 * (y + z) ^ 2 * (z + x)) / (2 * x + y + z) ^ 2 + (2 * (z + x) ^ 2 * (y + z)) / (2 * y + x + z) ^ 2 ↔
    z = ((y + z) ^ 2 * (z + x)) / (2 * x + y + z) ^ 2 + ((y + z) * (z + x) ^ 2) / (2 * y + x + z) ^ 2 := by
  intro x y z
  intros
  norm_num at * <;> first | omega | nlinarith | grind
