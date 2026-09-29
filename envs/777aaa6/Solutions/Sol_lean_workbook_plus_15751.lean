-- Prove2me | solution 1 for lean_workbook_plus_15751
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:12.115148+00:00
-- url     : https://prove2.me/submissions/38758f40-43b7-4ef0-abea-1a7fa718901c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℤ, (a + b) * (a - b) = a^2 - b^2 := by
  (intros; linarith)
