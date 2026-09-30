-- Prove2me | solution 1 for lean_workbook_plus_80763
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:14.617576+00:00
-- url     : https://prove2.me/submissions/06a0e89c-0601-4afc-9d09-fe1e9ade0d92

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution : ∀ x : ℝ, 0 < x ∧ x < 1 → 2 * x * (1 - x) ^ 2 ≤ 8 / 27 := by
  intro x hx
  have hs := mul_nonneg (sq_nonneg (1 - 3 * x)) (show 0 ≤ 4 - 3 * x by linarith [hx.2])
  nlinarith [hs]
