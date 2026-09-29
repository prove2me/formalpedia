-- Prove2me | solution 1 for lean_workbook_plus_26682
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:51.50139+00:00
-- url     : https://prove2.me/submissions/35884113-472b-4737-846e-5d658cbc9eed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = -3 / 2) (h₂ : x = -2) : (x, y) = (-2, -3 / 2) := by
  (intros; simp_all)
