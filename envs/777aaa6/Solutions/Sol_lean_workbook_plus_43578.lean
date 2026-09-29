-- Prove2me | solution 1 for lean_workbook_plus_43578
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:13.280809+00:00
-- url     : https://prove2.me/submissions/82da83ed-ac14-4e87-81ed-a962b2d37d2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a + b + c) / 3 = d - 8 ∧ (a + b + c + d) / 4 = 42 → (3 * d - 2 + d + 5) / 2 = 97.5 := by
  (intros; linarith)
