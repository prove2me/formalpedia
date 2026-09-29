-- Prove2me | solution 1 for lean_workbook_plus_61450
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:44.693413+00:00
-- url     : https://prove2.me/submissions/d00392e7-c89f-4aa7-9eb6-09dee8da3bfd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (a^2 + 1) + 2 / (b^2 + 1) = 1) : a * (4 * b - a) ≤ 6 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
