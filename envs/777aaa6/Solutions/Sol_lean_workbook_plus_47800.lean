-- Prove2me | solution 1 for lean_workbook_plus_47800
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:22.6705+00:00
-- url     : https://prove2.me/submissions/7a445006-abf9-440c-9bbc-e0ff95c06356

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (1 + a) + 2 / (1 + b) ≤ 1) : a * b^2 ≥ 8 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
