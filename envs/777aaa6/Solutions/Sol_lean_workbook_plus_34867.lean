-- Prove2me | solution 1 for lean_workbook_plus_34867
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:32.060266+00:00
-- url     : https://prove2.me/submissions/89189c66-f632-4b04-886c-d5822e5af070

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b k : ℤ) (h₁ : a + b = k) (h₂ : a * b = (k^2 - 2) / 2) : a * b = (k^2 - 2) / 2 := by
  (intros; simp_all)
