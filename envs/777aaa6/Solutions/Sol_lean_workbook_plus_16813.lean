-- Prove2me | solution 1 for lean_workbook_plus_16813
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:56.855709+00:00
-- url     : https://prove2.me/submissions/ad2c7091-c46b-429f-a8d2-bb197036126e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a : ℝ) (h₁ : f (0 + a) = 1 / 2 + Real.sqrt (f 0 - (f 0)^2)) : f a = 1 / 2 + Real.sqrt (f 0 - (f 0)^2) := by
  (intros; simp_all)
