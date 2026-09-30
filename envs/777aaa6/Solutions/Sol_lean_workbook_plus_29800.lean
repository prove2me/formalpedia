-- Prove2me | solution 1 for lean_workbook_plus_29800
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:01.804374+00:00
-- url     : https://prove2.me/submissions/5b6bac37-46ab-4c20-9574-99859648157c

import Mathlib
set_option autoImplicit false

theorem solution (k : ℤ) (h : k % 2 = 1) : ∃ n : ℤ, k ^ 2 = 8 * n + 1   := by
  have hc : k % 4 = 1 ∨ k % 4 = 3 := by omega
  rcases hc with hc | hc
  · have hk : k = 4 * (k / 4) + 1 := by omega
    refine ⟨2 * (k / 4) ^ 2 + k / 4, ?_⟩
    calc
      k ^ 2 = (4 * (k / 4) + 1) ^ 2 := congrArg (fun t : ℤ => t ^ 2) hk
      _ = 8 * (2 * (k / 4) ^ 2 + k / 4) + 1 := by ring
  · have hk : k = 4 * (k / 4) + 3 := by omega
    refine ⟨2 * (k / 4) ^ 2 + 3 * (k / 4) + 1, ?_⟩
    calc
      k ^ 2 = (4 * (k / 4) + 3) ^ 2 := congrArg (fun t : ℤ => t ^ 2) hk
      _ = 8 * (2 * (k / 4) ^ 2 + 3 * (k / 4) + 1) + 1 := by ring

#print axioms solution
