-- Prove2me | solution 1 for lean_workbook_plus_8739
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:51.519739+00:00
-- url     : https://prove2.me/submissions/64eca4f7-6f95-4d59-85c4-83d671c75f30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℤ, x^81 + x^49 + x^25 + x^9 + x = x * (x^80 - 1) + x * (x^48 - 1) + x * (x^24 - 1) + x * (x^8 - 1) + 5 * x := by
  (intros; linarith)
