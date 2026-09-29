-- Prove2me | solution 1 for lean_workbook_plus_55469
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:01.003942+00:00
-- url     : https://prove2.me/submissions/299b8cf4-ba62-49d3-9bb9-e5257ee4cc4b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (D : ℝ) (R : ℝ) (g_s : ℝ) (g : ℝ) (h₁ : R > D) (h₂ : g = g_s * (1 - D / R)) : g = g_s * (1 - D / R) := by
  (intros; simp_all)
