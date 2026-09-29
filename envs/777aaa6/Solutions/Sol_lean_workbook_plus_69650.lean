-- Prove2me | solution 1 for lean_workbook_plus_69650
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:31.063263+00:00
-- url     : https://prove2.me/submissions/8c5d87ef-a01d-4a9a-be8e-da73c2a1259a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x = x + 1 / 2) : ∀ x, f x = x + 1 / 2 := by
  (intros; simp_all)
