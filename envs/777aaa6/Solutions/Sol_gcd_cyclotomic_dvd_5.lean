-- Prove2me | solution 1 for gcd_cyclotomic_dvd_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:07:14.133469+00:00
-- url     : https://prove2.me/submissions/bb075fc8-32af-4cd3-8996-7dc61296e3bf

import Theorems.Thm_gcd_cyclotomic_dvd_5
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) : ℤ) ∣ 5 := by
  set D := Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) with hD_def
  have hD_ab : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) :=
    Int.gcd_dvd_right _ _
  -- D | 5*b^4 via ring identity
  have hD_5b4 : (D : ℤ) ∣ 5 * b ^ 4 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3), by
      have key : 5 * b ^ 4 = (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) -
          (a + b) * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) := by ring
      rw [key, hs, ht]; ring⟩
  -- D | (a+b).natAbs in ℕ
  have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
  -- gcd(a+b, b) = 1: use gcd_add_mul_right_right with b as first arg
  have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
    rw [Int.gcd_comm]
    -- goal: b.gcd (a + b) = 1
    have h := @Int.gcd_add_mul_right_right b a 1
    -- h : b.gcd (a + 1 * b) = b.gcd a
    simp only [one_mul] at h
    -- h : b.gcd (a + b) = b.gcd a
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
  -- Nat.Coprime D (b^4).natAbs
  have hcop_D_b4 : Nat.Coprime D (b ^ 4).natAbs := by
    rw [Int.natAbs_pow]
    exact hcop_D_b.pow_right 4
  -- D | 5*(b^4).natAbs via Int.natAbs_mul + norm_cast
  have hD_dvd_5b4_nat : D ∣ 5 * (b ^ 4).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_5b4
    rw [Int.natAbs_mul] at h
    -- h : (D:ℤ).natAbs ∣ (5:ℤ).natAbs * (b^4).natAbs
    norm_cast at h
  -- D | 5 in ℕ, then cast to ℤ
  exact_mod_cast hcop_D_b4.dvd_of_dvd_mul_right hD_dvd_5b4_nat
