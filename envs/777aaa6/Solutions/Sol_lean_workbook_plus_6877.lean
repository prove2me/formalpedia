-- Prove2me | solution 1 for lean_workbook_plus_6877
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:28.613013+00:00
-- url     : https://prove2.me/submissions/b46a89c1-1eb7-48db-80dd-06f79eecc028

import Mathlib
set_option autoImplicit false

theorem solution  (a b : ℝ)
  (n : ℕ)
  (u : ℕ → ℝ)
  (h₀ : u 0 = a * b)
  (h₁ : ∀ n, u (n + 1) = (1 + u n) / 2) :
  u n = 1 + (a * b - 1) / 2 ^ n   := by
  induction' n with n ih
  simp [h₀]
  simp [h₁, ih, pow_succ]
  ring

#print axioms solution
