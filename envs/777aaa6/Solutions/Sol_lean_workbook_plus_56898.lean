-- Prove2me | solution 1 for lean_workbook_plus_56898
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:57.933963+00:00
-- url     : https://prove2.me/submissions/4029bdd9-5919-45a4-89f2-e7a6ec772125

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) : a - c ≥ b - c ∧ b - c ≥ 0 := by
  (intros; simp_all)
