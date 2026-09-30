-- Prove2me | solution 1 for lean_workbook_plus_82717
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:00.35+00:00
-- url     : https://prove2.me/submissions/2c722269-9c60-43ad-9cb1-4afb7053a574

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℝ, 1 + x^2 ≥ 2*x ↔ (1-x)^2 ≥ 0 := by
  intro x
  constructor <;> intro h <;> nlinarith

#print axioms solution
