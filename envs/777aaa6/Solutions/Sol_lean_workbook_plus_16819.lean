-- Prove2me | solution 1 for lean_workbook_plus_16819
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:04.471713+00:00
-- url     : https://prove2.me/submissions/4105706f-9238-49a8-b24f-00c83b168b77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d h f : ℝ) (h₁ : a + b = c + d) (h₂ : h = f) : a + b + h = c + d + f := by
  (intros; simp_all)
