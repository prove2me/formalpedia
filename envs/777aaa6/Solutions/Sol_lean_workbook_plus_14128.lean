-- Prove2me | solution 1 for lean_workbook_plus_14128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:58.887563+00:00
-- url     : https://prove2.me/submissions/a55caaaa-94b4-406a-8c28-80d788d834e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) : (2*x-1 = -25 ∨ 2*x-1 = -5 ∨ 2*x-1 = -1 ∨ 2*x-1 = 1 ∨ 2*x-1 = 5 ∨ 2*x-1 = 25) ↔ x = -12 ∨ x = -2 ∨ x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 13 := by
  (intros; omega)
