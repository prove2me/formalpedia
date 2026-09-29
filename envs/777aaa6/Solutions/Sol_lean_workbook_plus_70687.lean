-- Prove2me | solution 1 for lean_workbook_plus_70687
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:13.827911+00:00
-- url     : https://prove2.me/submissions/72325b71-4c7e-4dd7-9111-8158327d32d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (h1 : a + b + c = 2 * a) (h2 : a + b + c = 2 * b) (h3 : a + b + c = 2 * c) : a = b ∧ b = c ∧ c = a := by
  (intros; simp_all)
