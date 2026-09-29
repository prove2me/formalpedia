-- Prove2me | solution 1 for lean_workbook_plus_3575
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:49.309205+00:00
-- url     : https://prove2.me/submissions/7eaf3218-90c8-475a-965d-6fb980f1c250

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
  (intros; omega)
