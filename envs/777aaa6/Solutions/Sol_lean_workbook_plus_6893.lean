-- Prove2me | solution 1 for lean_workbook_plus_6893
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:37.624932+00:00
-- url     : https://prove2.me/submissions/b394bba0-335d-42a6-95df-b282d5a5ffa4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ k : ℤ, 22 * (3 * k - 1) + 6 * (4 - 11 * k) = 2 := by
  (intros; omega)
