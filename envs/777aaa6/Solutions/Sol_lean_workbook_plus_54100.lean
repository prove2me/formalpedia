-- Prove2me | solution 1 for lean_workbook_plus_54100
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:18.007627+00:00
-- url     : https://prove2.me/submissions/23e88950-4b4a-4397-a5a3-d026471c9c52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 2 < x)
  (h₁ : x < 3)
  (h₂ : 0 < x) :
  2 < x ∧ x < 3 := by
  (intros; simp_all)
