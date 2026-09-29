-- Prove2me | solution 1 for lean_workbook_plus_26977
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:38.876731+00:00
-- url     : https://prove2.me/submissions/79d0cd35-9b71-40a8-aab4-d6aac89d0526

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a : ℤ, a % 3 = 0 → (a - 1) % 3 = 2 ∧ (2 * a + 1) % 3 = 1 := by
  (intros; omega)
