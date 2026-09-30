-- Prove2me | solution 1 for lean_workbook_plus_68739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:13.935274+00:00
-- url     : https://prove2.me/submissions/1fe12dee-8e15-4112-ad23-fb2e6f0cda3c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2 + 3) * (b ^ 2 + 3) ≥ 8 * (a + b) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a + b - 2), sq_nonneg (a - b)]
