-- Prove2me | solution 1 for lean_workbook_plus_9177
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:55.570686+00:00
-- url     : https://prove2.me/submissions/a7c5bb33-89cd-4629-af3b-85aeac3f33b5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a = 3) (h₂ : b = a * Real.sqrt 2) : b = 3 * Real.sqrt 2 := by
  (intros; simp_all)
