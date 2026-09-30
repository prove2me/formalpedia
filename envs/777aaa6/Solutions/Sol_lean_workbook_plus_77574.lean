-- Prove2me | solution 1 for lean_workbook_plus_77574
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:06.350688+00:00
-- url     : https://prove2.me/submissions/9f060884-6285-4e3e-8a77-9b0ef91d6bfe

import Mathlib

theorem solution (n : ℕ) (h₁ : n ≡ 0 [ZMOD 2]) (h₂ : 5 ∣ n) : 10 ∣ n := by
  have htwo : (2 : ℤ) ∣ (n : ℤ) := Int.modEq_zero_iff_dvd.mp h₁
  have htwoNat : 2 ∣ n := by exact_mod_cast htwo
  exact (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd htwoNat h₂
