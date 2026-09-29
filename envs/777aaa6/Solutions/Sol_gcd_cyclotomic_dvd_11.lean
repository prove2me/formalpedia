-- Prove2me | solution 1 for gcd_cyclotomic_dvd_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T06:35:07.127589+00:00
-- url     : https://prove2.me/submissions/e7d29929-defc-47b4-aec0-ea5efa79bf6a

import Theorems.Thm_gcd_cyclotomic_dvd_11
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Phi11(a,b) = a^10 - a^9*b + a^8*b^2 - ... - a*b^9 + b^10
-- Ring identity: 11*b^10 = Phi11 - (a+b)*Q11
-- Q11 = a^9 - 2a^8b + 3a^7b^2 - 4a^6b^3 + 5a^5b^4 - 6a^4b^5 + 7a^3b^6 - 8a^2b^7 + 9ab^8 - 10b^9

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 -
      a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) : ℤ) ∣ 11 := by
  set D := Int.gcd (a + b) (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 -
      a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) with hD_def
  have hD_ab : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 + a ^ 6 * b ^ 4 -
      a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 - a * b ^ 9 + b ^ 10) :=
    Int.gcd_dvd_right _ _
  -- D | 11*b^10 via ring identity
  have hD_11b10 : (D : ℤ) ∣ 11 * b ^ 10 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 9 - 2 * a ^ 8 * b + 3 * a ^ 7 * b ^ 2 - 4 * a ^ 6 * b ^ 3 +
        5 * a ^ 5 * b ^ 4 - 6 * a ^ 4 * b ^ 5 + 7 * a ^ 3 * b ^ 6 - 8 * a ^ 2 * b ^ 7 +
        9 * a * b ^ 8 - 10 * b ^ 9), by
      have key : 11 * b ^ 10 = (a ^ 10 - a ^ 9 * b + a ^ 8 * b ^ 2 - a ^ 7 * b ^ 3 +
          a ^ 6 * b ^ 4 - a ^ 5 * b ^ 5 + a ^ 4 * b ^ 6 - a ^ 3 * b ^ 7 + a ^ 2 * b ^ 8 -
          a * b ^ 9 + b ^ 10) - (a + b) * (a ^ 9 - 2 * a ^ 8 * b + 3 * a ^ 7 * b ^ 2 -
          4 * a ^ 6 * b ^ 3 + 5 * a ^ 5 * b ^ 4 - 6 * a ^ 4 * b ^ 5 + 7 * a ^ 3 * b ^ 6 -
          8 * a ^ 2 * b ^ 7 + 9 * a * b ^ 8 - 10 * b ^ 9) := by ring
      rw [key, hs, ht]; ring⟩
  have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
  have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
    rw [Int.gcd_comm]
    have h := @Int.gcd_add_mul_right_right b a 1
    simp only [one_mul] at h
    rw [h, Int.gcd_comm]; exact hab
  have hcop_D_b : Nat.Coprime D b.natAbs := by
    unfold Nat.Coprime
    apply Nat.eq_one_of_dvd_one
    have h1 : Nat.gcd D b.natAbs ∣ D := Nat.gcd_dvd_left D b.natAbs
    have h2 : Nat.gcd D b.natAbs ∣ b.natAbs := Nat.gcd_dvd_right D b.natAbs
    have h3 : Nat.gcd D b.natAbs ∣ (a + b).natAbs := dvd_trans h1 hD_dvd_ab_nat
    have h4 : Nat.gcd D b.natAbs ∣ Nat.gcd (a + b).natAbs b.natAbs := Nat.dvd_gcd h3 h2
    rwa [show Nat.gcd (a + b).natAbs b.natAbs = 1 from hgcd_ab_b] at h4
  have hcop_D_b10 : Nat.Coprime D (b ^ 10).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 10
  have hD_dvd_11b10_nat : D ∣ 11 * (b ^ 10).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_11b10
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b10.dvd_of_dvd_mul_right hD_dvd_11b10_nat
