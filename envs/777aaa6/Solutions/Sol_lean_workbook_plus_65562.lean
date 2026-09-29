-- Prove2me | solution 1 for lean_workbook_plus_65562
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:25.796848+00:00
-- url     : https://prove2.me/submissions/8392807b-8a11-4fd3-94ec-455ff02056df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (q e : ℚ)
  (h₀ : q = -1)
  (h₁ : e = 1 / -1) :
  q = e := by
  (intros; simp_all)
