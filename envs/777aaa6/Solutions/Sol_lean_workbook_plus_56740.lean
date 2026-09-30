-- Prove2me | solution 1 for lean_workbook_plus_56740
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:40.015005+00:00
-- url     : https://prove2.me/submissions/1a66786a-9f2d-4d8e-97eb-b705444a59c7

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : (5*x-6-x^2)/2 ≥ 0 ↔ 2 ≤ x ∧ x ≤ 3   := by
  constructor
  intro h
  constructor <;> nlinarith [h]
  rintro ⟨h2, h3⟩
  nlinarith

#print axioms solution
