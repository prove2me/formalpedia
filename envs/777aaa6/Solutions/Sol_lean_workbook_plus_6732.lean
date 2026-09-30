-- Prove2me | solution 1 for lean_workbook_plus_6732
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:29.36589+00:00
-- url     : https://prove2.me/submissions/e8fd0444-ce31-4a52-87a4-e76ba0bee570

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (f_def : ∀ x, x < 5 → f x = 3 * x + 6 ∧ ∀ x, 5 ≤ x → f x = 7 * x - 20) : f (f (f 2)) = 428   := by
  have h := f_def 2 (by norm_num)
  have h2 : f 2 = 12 := by linarith [h.1]
  have h12 : f 12 = 64 := by
    have hi := h.2 12 (by norm_num)
    linarith
  have h64 : f 64 = 428 := by
    have hi := h.2 64 (by norm_num)
    linarith
  rw [h2, h12, h64]

#print axioms solution
