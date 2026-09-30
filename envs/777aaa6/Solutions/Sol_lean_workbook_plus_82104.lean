-- Prove2me | solution 1 for lean_workbook_plus_82104
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:12:56.048177+00:00
-- url     : https://prove2.me/submissions/12b6de58-d79a-4528-aeee-e8c5c86ce0af

import Mathlib
set_option autoImplicit false

theorem solution : ∀ n : ℕ, 2 ∣ (1111^n - 1109^n) := by
  intro n
  have h : 1109^n ≡ 1111^n [MOD 2] :=
    (show 1109 ≡ 1111 [MOD 2] from by decide).pow n
  exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left (by decide) n)).mp h

#print axioms solution
