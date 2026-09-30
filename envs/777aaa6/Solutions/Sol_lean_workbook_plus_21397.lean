-- Prove2me | solution 1 for lean_workbook_plus_21397
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:51.667922+00:00
-- url     : https://prove2.me/submissions/4e8a3831-c25f-429c-acf1-e21b758802a9

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

theorem solution : ∀ n : ℕ, 17 ∣ 3 * 5 ^ (2 * n + 1) + 2 ^ (3 * n + 1) := by
  intro n
  have h : Nat.ModEq 17 (3 * 5 ^ (2 * n + 1) + 2 ^ (3 * n + 1)) (17 * 8 ^ n) := by
    convert (((show Nat.ModEq 17 25 8 from by decide).pow n).mul_left 15).add
      (Nat.ModEq.refl (2 * 8 ^ n)) using 1
    · simp [pow_add, pow_mul]
      ring
    · ring
  exact (h.dvd_iff (dvd_refl 17)).mpr (dvd_mul_right 17 (8 ^ n))
