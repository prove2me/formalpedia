-- Prove2me | solution 1 for lean_workbook_plus_4799
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:22.530743+00:00
-- url     : https://prove2.me/submissions/e9cf50f6-299f-4fab-8398-a1473fd13dfe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (q e : ℚ)
  (h₀ : q = 3 / 5)
  (h₁ : e = 1 / 5) :
  q + e = 4 / 5 := by
  (intros; linarith)
