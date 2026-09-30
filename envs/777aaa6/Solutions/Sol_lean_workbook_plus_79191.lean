-- Prove2me | solution 1 for lean_workbook_plus_79191
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:03.210027+00:00
-- url     : https://prove2.me/submissions/b7d91063-74f0-4c00-be84-c43c8a08e246

import Mathlib

theorem solution (n : ℕ) : 3 ∣ 10^(n+1) + 10^n + 1 := by
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
