-- Prove2me | solution 1 for lean_workbook_plus_80237
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:53.046883+00:00
-- url     : https://prove2.me/submissions/b9a33b02-2c24-48d9-9181-68e7e3cb46d8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ a b c : ℝ,
    3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) +
      (a + b + c) * (a^3 + b^3 + c^3) ≥
        2 / 3 * (a^2 + b^2 + c^2) * (a + b + c)^2 := by
  intro a b c
  nlinarith [sq_nonneg ((a - b) * (a + b - c)),
    sq_nonneg ((b - c) * (b + c - a)),
    sq_nonneg ((c - a) * (c + a - b)),
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
    sq_nonneg (c * a - a * b)]
