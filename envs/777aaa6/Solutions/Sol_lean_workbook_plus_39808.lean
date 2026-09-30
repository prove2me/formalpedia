-- Prove2me | solution 1 for lean_workbook_plus_39808
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:27.15972+00:00
-- url     : https://prove2.me/submissions/93d3d242-375d-4e08-bde0-f029d45a2543

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a < b ∧ b < c) (h₂ : a + b + c = 0) : (a^2 + b^2 + c^2) / (c - a)^2 < 2 / 3   := by
  have hd : 0 < (c - a)^2 := pow_pos (sub_pos.mpr (lt_trans h₁.1 h₁.2)) 2
  have hp : 0 < (b - a) * (c - b) :=
    mul_pos (sub_pos.mpr h₁.1) (sub_pos.mpr h₁.2)
  have hgap : 2 * (c - a)^2 - 3 * (a^2 + b^2 + c^2) = 2 * (b - a) * (c - b) := by
    linear_combination (-(a + b + c)) * h₂
  apply (div_lt_iff₀ hd).2
  nlinarith only [hgap, hp]

#print axioms solution
