-- Prove2me | solution 1 for gcd_cyclotomic_dvd_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:09:19.218834+00:00
-- url     : https://prove2.me/submissions/0a867dbd-897b-4cab-b351-f973d98435e8

import Theorems.Thm_gcd_cyclotomic_dvd_13
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Q13 = sum_{k=0}^{11} (-1)^k*(k+1)*a^(11-k)*b^k  (12 terms, degree 11)
-- Key: 13*b^12 = Phi13(a,b) - (a+b)*Q13(a,b)

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
      a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
      a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) : ℤ) ∣ 13 := by
  set D := Int.gcd (a + b) (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
      a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
      a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12)
  have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
      a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
      a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) := Int.gcd_dvd_right _ _
  have hD_13b12 : (D : ℤ) ∣ 13 * b ^ 12 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 11 - 2 * a ^ 10 * b + 3 * a ^ 9 * b ^ 2 - 4 * a ^ 8 * b ^ 3 +
        5 * a ^ 7 * b ^ 4 - 6 * a ^ 6 * b ^ 5 + 7 * a ^ 5 * b ^ 6 - 8 * a ^ 4 * b ^ 7 +
        9 * a ^ 3 * b ^ 8 - 10 * a ^ 2 * b ^ 9 + 11 * a * b ^ 10 - 12 * b ^ 11), by
      have key : 13 * b ^ 12 =
          (a ^ 12 - a ^ 11 * b + a ^ 10 * b ^ 2 - a ^ 9 * b ^ 3 + a ^ 8 * b ^ 4 -
          a ^ 7 * b ^ 5 + a ^ 6 * b ^ 6 - a ^ 5 * b ^ 7 + a ^ 4 * b ^ 8 - a ^ 3 * b ^ 9 +
          a ^ 2 * b ^ 10 - a * b ^ 11 + b ^ 12) -
          (a + b) * (a ^ 11 - 2 * a ^ 10 * b + 3 * a ^ 9 * b ^ 2 - 4 * a ^ 8 * b ^ 3 +
          5 * a ^ 7 * b ^ 4 - 6 * a ^ 6 * b ^ 5 + 7 * a ^ 5 * b ^ 6 - 8 * a ^ 4 * b ^ 7 +
          9 * a ^ 3 * b ^ 8 - 10 * a ^ 2 * b ^ 9 + 11 * a * b ^ 10 - 12 * b ^ 11) := by ring
      rw [key, hs, ht]; ring⟩
  have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
  have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
    rw [Int.gcd_comm]
    have h := @Int.gcd_add_mul_right_right b a 1
    simp only [one_mul] at h
    rw [h, Int.gcd_comm]; exact hab
  have hcop_D_b : Nat.Coprime D b.natAbs := by
    unfold Nat.Coprime; apply Nat.eq_one_of_dvd_one
    have h1 := Nat.gcd_dvd_left D b.natAbs
    have h2 := Nat.gcd_dvd_right D b.natAbs
    have h3 : Nat.gcd D b.natAbs ∣ (a + b).natAbs := dvd_trans h1 hD_dvd_ab_nat
    have h4 := Nat.dvd_gcd h3 h2
    rwa [show Nat.gcd (a + b).natAbs b.natAbs = 1 from hgcd_ab_b] at h4
  have hcop_D_b12 : Nat.Coprime D (b ^ 12).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 12
  have hD_dvd_13b12_nat : D ∣ 13 * (b ^ 12).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_13b12
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b12.dvd_of_dvd_mul_right hD_dvd_13b12_nat
