-- Prove2me | solution 1 for lean_workbook_plus_67313
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:32.367072+00:00
-- url     : https://prove2.me/submissions/1c25e26a-2a83-4ef6-80c4-44620e9c73fa

import Mathlib
set_option autoImplicit false

theorem solution : ∀ n : ℤ, n % 2 = 1 → 4 ∣ (n + 1) * (n - 1)   := by
  intro n hn
  have he : n = 2 * (n / 2) + 1 := by omega
  refine ⟨(n / 2 + 1) * (n / 2), ?_⟩
  calc
    (n + 1) * (n - 1) = (2 * (n / 2) + 1 + 1) * (2 * (n / 2) + 1 - 1) := by rw [← he]
    _ = 4 * ((n / 2 + 1) * (n / 2)) := by ring

#print axioms solution
