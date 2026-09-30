-- Prove2me | solution 1 for lean_workbook_plus_51377
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:44.57346+00:00
-- url     : https://prove2.me/submissions/f3150897-0313-48e2-a72e-1a09ae5f0f8a

import Mathlib
set_option autoImplicit false

theorem solution (t : ℝ) (d₁ d₂ : ℝ) (h₁ : d₁ = t * 13.5) (h₂ : d₂ = (t-7) * 15) : d₁ = d₂ ↔ t = 70   := by
  rw [h₁, h₂]
  ring_nf
  constructor <;> intro h
  linarith
  linarith [h]

#print axioms solution
