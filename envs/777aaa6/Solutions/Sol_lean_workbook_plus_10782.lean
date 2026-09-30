-- Prove2me | solution 1 for lean_workbook_plus_10782
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:36.507103+00:00
-- url     : https://prove2.me/submissions/fcadc0b3-abe2-44de-83c6-54933c9f8b73

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n)
    (h₂ : n ^ 4 = n ^ 3 + 13 * n ^ 2 + 36 * n + 39) : False := by
  obtain ⟨k, rfl⟩ := h₁
  ring_nf at h₂
  omega

#print axioms solution
