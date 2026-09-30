-- Prove2me | solution 1 for lean_workbook_plus_77109
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:54.696274+00:00
-- url     : https://prove2.me/submissions/2d29a8a1-414b-4b99-947d-98fe8290eda1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 →
    (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by
  rintro a b c ⟨ha, hb, hc⟩
  nlinarith [mul_nonneg ha.le (sq_nonneg (b - c)),
    mul_nonneg hb.le (sq_nonneg (c - a)),
    mul_nonneg hc.le (sq_nonneg (a - b))]
