-- Prove2me | solution 1 for lean_workbook_plus_42894
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:44.683298+00:00
-- url     : https://prove2.me/submissions/a6df019c-4bff-456a-b18f-d9e2a1975367

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x = 1)
  (h₁ : x^2 - 1 = 0) :
  (x + 1) * (x - 1) = 0 := by
  (intros; simp_all)
