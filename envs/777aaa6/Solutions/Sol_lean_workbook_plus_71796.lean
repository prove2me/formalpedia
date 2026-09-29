-- Prove2me | solution 1 for lean_workbook_plus_71796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:45.023576+00:00
-- url     : https://prove2.me/submissions/ec21a5fd-fa09-400f-b991-1dbde8e41b0e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c ≥ 27 / 8) → (8 * a * b + 8 * b * c + 8 * c * a ≥ 27 * a * b * c) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
