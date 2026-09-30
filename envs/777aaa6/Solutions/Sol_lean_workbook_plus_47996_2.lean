-- Prove2me | solution 2 for lean_workbook_plus_47996
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:24.256194+00:00
-- url     : https://prove2.me/submissions/092bd8bc-2fef-403b-a095-55e257f4fab2

import Mathlib
set_option autoImplicit false

theorem solution : ∀ {a a' m : ℕ}, a ≡ a' [ZMOD m] → ∀ n : ℕ, a ^ n ≡ a' ^ n [ZMOD m]   := by
  exact fun {a a' m} h n ↦ h.pow n

#print axioms solution
