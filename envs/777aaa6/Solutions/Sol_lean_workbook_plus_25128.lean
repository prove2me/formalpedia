-- Prove2me | solution 1 for lean_workbook_plus_25128
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:12:11.982054+00:00
-- url     : https://prove2.me/submissions/6cab84ea-9d23-44ea-b94e-75f5f7b5389a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (b c : ℝ) : (b + c) ^ 4 ≤ 16 * (b ^ 4 - b ^ 2 * c ^ 2 + c ^ 4) := by
  nlinarith only [sq_nonneg ((b - c) * (b + c)), sq_nonneg ((b - c) ^ 2)]
