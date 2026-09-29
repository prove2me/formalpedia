-- Prove2me | solution 1 for lean_workbook_plus_32727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:38.282536+00:00
-- url     : https://prove2.me/submissions/708c9fc4-6d82-4ed3-94c4-134af5eebc4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b: ℝ) : (|a| * |b| ≤ |a| + |b|) → (|a| - 1) * (|b| - 1) ≤ 1 := by
  (intros; linarith)
