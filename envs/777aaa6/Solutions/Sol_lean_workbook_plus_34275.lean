-- Prove2me | solution 1 for lean_workbook_plus_34275
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:52.846146+00:00
-- url     : https://prove2.me/submissions/658f9833-10ec-4964-8b17-f1c1bbb2ad31

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a ≤ b ∧ b ≤ c → 3 * a ≤ a + b + c - Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)   := by
  intro a b c h
  have hp : 0 ≤ (b - a) * (c - a) :=
    mul_nonneg (by linarith [h.1]) (by linarith [h.1, h.2])
  have hb : Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) ≤ b + c - 2 * a :=
    (Real.sqrt_le_iff).2 ⟨by linarith [h.1, h.2], by nlinarith only [hp]⟩
  linarith

#print axioms solution
