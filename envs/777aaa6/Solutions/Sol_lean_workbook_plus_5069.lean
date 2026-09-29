-- Prove2me | solution 1 for lean_workbook_plus_5069
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:52.379729+00:00
-- url     : https://prove2.me/submissions/10b9d1d0-a252-4b0d-9eea-ed9c09bf9407

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) = 9) : a * b ≤ 1 / 3 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
