-- Prove2me | solution 1 for gcd_coprime_pow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:12:40.080272+00:00
-- url     : https://prove2.me/submissions/a6fc9f00-f8fc-41e3-b6ec-0c20dea6439e

import Theorems.Thm_gcd_coprime_pow
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem solution (a b : ℤ) (n : ℕ) (h : Int.gcd a b = 1) : Int.gcd a (b ^ n) = 1 := by
  have hcop : Nat.Coprime a.natAbs b.natAbs := h
  have hcop_pow : Nat.Coprime a.natAbs (b ^ n).natAbs := by
    rw [Int.natAbs_pow]
    exact hcop.pow_right n
  exact hcop_pow
