-- Prove2me | solution 1 for lean_workbook_plus_34119
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:14.341624+00:00
-- url     : https://prove2.me/submissions/d234fb60-0963-4a56-b6ac-a1742ed98722

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a + b ≥ 2 * Real.sqrt (a * b) → (Real.sqrt a - Real.sqrt b) ^ 2 ≥ 0 := by
  (intros; positivity)
