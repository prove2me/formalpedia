-- Prove2me | solution 1 for lean_workbook_plus_18953
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:25.383481+00:00
-- url     : https://prove2.me/submissions/be4e9126-b8c1-4875-9ecd-7410723a8d7b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x^2 = y^2 + z^2) : (x^2 + y^2 - z^2) * (y^2 + z^2 - x^2) * (z^2 + x^2 - y^2) = 0 := by
  (intros; simp_all)
