-- Prove2me | solution 1 for lean_workbook_plus_61362
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:48.478022+00:00
-- url     : https://prove2.me/submissions/41b208fe-8cf1-4821-b1e4-7b70ff239c35

import Mathlib
set_option autoImplicit false

theorem solution (r s t : ℤ) (h : r ≠ 0)  (h2 : r∣s*t) : r^2 ∣ s^2 * t^2   := by
  rcases h2 with ⟨k, hk⟩
  refine ⟨k ^ 2, ?_⟩
  calc
    s ^ 2 * t ^ 2 = (s * t) ^ 2 := by ring
    _ = (r * k) ^ 2 := by rw [hk]
    _ = r ^ 2 * k ^ 2 := by ring

#print axioms solution
