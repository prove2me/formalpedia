-- Prove2me | solution 1 for lean_workbook_plus_12049
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:05.495909+00:00
-- url     : https://prove2.me/submissions/0fe6ab56-3a51-4d39-b519-d085a8d84e58

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℝ, a^2 + 5 * a * b + 6 * b^2 = 0 → (a + 2 * b) * (a + 3 * b) = 0 := by
  (intros; linarith)
