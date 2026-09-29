-- Prove2me | solution 1 for gcd_cyclotomic_dvd_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:24:03.652731+00:00
-- url     : https://prove2.me/submissions/8b78a470-64fc-4653-8792-37f5989c378a

import Theorems.Thm_gcd_cyclotomic_dvd_3
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 2 - a * b + b ^ 2) : ℤ) ∣ 3 := by
  set D := Int.gcd (a + b) (a ^ 2 - a * b + b ^ 2) with hD_def
  have hD_ab : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 2 - a * b + b ^ 2) := Int.gcd_dvd_right _ _
  -- D | 3*b^2 via ring identity: 3b^2 = (a^2-ab+b^2) - (a+b)*(a-2b)
  have hD_3b2 : (D : ℤ) ∣ 3 * b ^ 2 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a - 2 * b), by
      have key : 3 * b ^ 2 = (a ^ 2 - a * b + b ^ 2) - (a + b) * (a - 2 * b) := by ring
      rw [key, hs, ht]; ring⟩
  -- D | (a+b).natAbs in ℕ
  have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
  -- gcd(a+b, b) = 1
  have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
    rw [Int.gcd_comm]
    have h := @Int.gcd_add_mul_right_right b a 1
    simp only [one_mul] at h
    rw [h, Int.gcd_comm]
    exact hab
  -- Nat.Coprime D b.natAbs via dvd chain
  have hcop_D_b : Nat.Coprime D b.natAbs := by
    unfold Nat.Coprime
    apply Nat.eq_one_of_dvd_one
    have h1 : Nat.gcd D b.natAbs ∣ D := Nat.gcd_dvd_left D b.natAbs
    have h2 : Nat.gcd D b.natAbs ∣ b.natAbs := Nat.gcd_dvd_right D b.natAbs
    have h3 : Nat.gcd D b.natAbs ∣ (a + b).natAbs := dvd_trans h1 hD_dvd_ab_nat
    have h4 : Nat.gcd D b.natAbs ∣ Nat.gcd (a + b).natAbs b.natAbs :=
      Nat.dvd_gcd h3 h2
    rwa [show Nat.gcd (a + b).natAbs b.natAbs = 1 from hgcd_ab_b] at h4
  -- Nat.Coprime D (b^2).natAbs
  have hcop_D_b2 : Nat.Coprime D (b ^ 2).natAbs := by
    rw [Int.natAbs_pow]
    exact hcop_D_b.pow_right 2
  -- D | 3*(b^2).natAbs via Int.natAbs_mul + norm_cast
  have hD_dvd_3b2_nat : D ∣ 3 * (b ^ 2).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_3b2
    rw [Int.natAbs_mul] at h
    norm_cast at h
  -- D | 3 in ℕ, then cast to ℤ
  exact_mod_cast hcop_D_b2.dvd_of_dvd_mul_right hD_dvd_3b2_nat
