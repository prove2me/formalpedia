-- Prove2me | solution 1 for lean_workbook_plus_25051
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:54.412713+00:00
-- url     : https://prove2.me/submissions/c26cf658-e987-42b2-a950-e89d096beaf6

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (f : ℝ → ℝ) (hf: f = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : f 1 = 10 ∧ f 2 = 20 ∧ f 3 = 30 → (f 12 + f (-8)) / 10 = 1984   := by
  rw [hf]
  rintro ⟨h1, h2, h3⟩
  norm_num at h1 h2 h3 ⊢
  linear_combination (norm := ring_nf) 10 * h1 - (99 / 5 : ℝ) * h2 + 10 * h3
  exact (by ring : (-2048 : ℝ) / 5 + b * (-32 / 5) + b * 64 * (1 / 10) +
    4096 * (1 / 10) = 0)

#print axioms solution
