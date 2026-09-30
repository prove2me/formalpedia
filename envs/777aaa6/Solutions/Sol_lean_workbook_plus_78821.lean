-- Prove2me | solution 1 for lean_workbook_plus_78821
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:10:00.803278+00:00
-- url     : https://prove2.me/submissions/f974268d-6def-46bc-9024-b239d4b1d21e

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) : 8 ∣ 9 ^ n - 1 := by
  have hp : 0 < (9 : ℕ) ^ n := pow_pos (by decide) n
  apply (Nat.modEq_iff_dvd' (by omega : 1 ≤ 9 ^ n)).1
  simpa only [one_pow] using (show 1 ≡ 9 [MOD 8] by decide).pow n
