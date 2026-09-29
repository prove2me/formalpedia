-- Prove2me | solution 1 for lean_workbook_plus_22881
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:46.777525+00:00
-- url     : https://prove2.me/submissions/dde48545-e43f-431d-b095-6b660428394f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : a ≥ 1) : 9 * a ^ 10 ≥ 8 * a + 1 := by
  have hp : a ≤ a^10 := le_self_pow₀ h (by norm_num)
  linarith
