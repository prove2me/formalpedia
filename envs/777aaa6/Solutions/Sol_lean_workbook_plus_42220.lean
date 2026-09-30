-- Prove2me | solution 1 for lean_workbook_plus_42220
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:52.539459+00:00
-- url     : https://prove2.me/submissions/24f9d685-cb45-44f8-a34d-66c71bfeb1f8

import Mathlib
set_option autoImplicit false

theorem solution {a b c : ℂ} (h : (a - b) * (b - c) * (c - a) = 0) :
  a = b ∨ b = c ∨ c = a   := by
  rw [mul_assoc] at h
  simp [sub_eq_zero] at h
  aesop

#print axioms solution
