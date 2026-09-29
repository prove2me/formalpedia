-- Prove2me | solution 1 for lean_workbook_plus_29773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:01.26755+00:00
-- url     : https://prove2.me/submissions/6fbb1de0-e05d-48e0-9e18-9d937a6bbe75

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b : ℝ, 2 * (a^2 - 2 * a * b + b^2 + 4) / (a^2 + 1) / (b^2 + 1) ≥ 0 := by
  intro a b
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
