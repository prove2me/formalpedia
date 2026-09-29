-- Prove2me | solution 1 for lean_workbook_plus_69072
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:12.212539+00:00
-- url     : https://prove2.me/submissions/e181bb08-7848-4303-80e0-d287e7935637

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) : (∀ x y, f x = f y → x = y) ↔ Function.Injective f := by
  rfl
