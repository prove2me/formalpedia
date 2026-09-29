-- Prove2me | solution 1 for lean_workbook_plus_47929
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:50.145218+00:00
-- url     : https://prove2.me/submissions/332b931a-7314-4161-84f9-bfd41569e70c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a - b) ^ 2 * (a + b) ≥ 0 → a ^ 3 + b ^ 3 ≥ a ^ 2 * b + a * b ^ 2 := by
  (intros; linarith)
