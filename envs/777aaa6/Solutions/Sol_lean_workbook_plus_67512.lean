-- Prove2me | solution 1 for lean_workbook_plus_67512
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:28.977775+00:00
-- url     : https://prove2.me/submissions/0997d988-4a4e-4623-b37b-6f857d33af80

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ (x : ℝ) (f g : ℝ → ℝ), (∀ x, f x = x^9 * (x + 1)) → (∀ x, g x = x^10 - 9 * x^9 + 10 * x^11) → 0 < x → g x - f x = x^9 * (10 * x - 9) * (x + 1)) := by
  intro h
  have bad := h 1 (fun x => x ^ 9 * (x + 1))
    (fun x => x ^ 10 - 9 * x ^ 9 + 10 * x ^ 11)
    (fun _ => rfl) (fun _ => rfl) (by norm_num)
  norm_num at bad

#print axioms solution
