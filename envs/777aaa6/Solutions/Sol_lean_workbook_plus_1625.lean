-- Prove2me | solution 1 for lean_workbook_plus_1625
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:49.335042+00:00
-- url     : https://prove2.me/submissions/1af78505-e37c-408a-ab4d-6b36b96d092a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (x : ℝ) (h₁ : 0 < a ∧ a < 1) (h₂ : x = 2 + a) : a = x - 2 := by
  (intros; simp_all)
