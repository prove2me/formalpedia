-- Prove2me | solution 1 for lean_workbook_plus_24976
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:23.164019+00:00
-- url     : https://prove2.me/submissions/59640287-4414-417c-beee-50584fd11f9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: ∀ n, f n = n - 1) : ∀ n < 80, f n = n - 1 := by
  (intros; simp_all)
