-- Prove2me | solution 1 for lean_workbook_plus_60749
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:34.06568+00:00
-- url     : https://prove2.me/submissions/76e25dbd-fff3-46f6-8597-a43c1bd1d36f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => -x / 3) : ∀ x, f x = -x / 3 := by
  (intros; simp_all)
