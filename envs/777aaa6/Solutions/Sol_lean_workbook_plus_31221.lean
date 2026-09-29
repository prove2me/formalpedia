-- Prove2me | solution 1 for lean_workbook_plus_31221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:34.020423+00:00
-- url     : https://prove2.me/submissions/4fa34c47-6eba-4560-81dc-54685800affc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 2 * 2 * x / (2 + x) = 3) :
  x = 6 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x]
