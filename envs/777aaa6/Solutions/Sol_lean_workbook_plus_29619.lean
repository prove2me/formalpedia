-- Prove2me | solution 1 for lean_workbook_plus_29619
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:41:59.804097+00:00
-- url     : https://prove2.me/submissions/8ecad37a-df86-4cbc-8e15-499c0ffa4841

import Mathlib
set_option autoImplicit false

theorem solution {a b c : ℕ} (h₁ : a + b = c) : (2^a) * (2^b) = (2^c)   := by
  simp only [←pow_add, h₁]

#print axioms solution
