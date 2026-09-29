-- Prove2me | solution 1 for lean_workbook_plus_62341
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:42.552116+00:00
-- url     : https://prove2.me/submissions/ca686731-e531-4739-adcf-3e8da365c351

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x = (4*y - 1) / y) (h₂ : z = 1 / (1 - y)) : x = (4*y - 1) / y ∧ z = 1 / (1 - y) := by
  (intros; simp_all)
