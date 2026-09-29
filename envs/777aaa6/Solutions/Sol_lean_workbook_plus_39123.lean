-- Prove2me | solution 1 for lean_workbook_plus_39123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:18.237439+00:00
-- url     : https://prove2.me/submissions/ea19b722-b1b0-4026-8834-e2f8e184e157

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b : ℝ} (ha : a > 0) (hb : b > 0) : (1 / a + 1 / b) / 2 ≥ 2 / (a + b) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
