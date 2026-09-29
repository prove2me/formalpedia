-- Prove2me | solution 1 for gcd_cyclotomic_dvd_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:20:12.071041+00:00
-- url     : https://prove2.me/submissions/1cf3c5c9-82f9-44ca-a1e2-b9267dc679ba

import Theorems.Thm_gcd_cyclotomic_dvd_17
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Q17 = sum_{k=0}^{15} (-1)^k*(k+1)*a^(15-k)*b^k  (16 terms, degree 15)
-- Key: 17*b^16 = Phi17(a,b) - (a+b)*Q17(a,b)

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 16 - a ^ 15 * b + a ^ 14 * b ^ 2 - a ^ 13 * b ^ 3 + a ^ 12 * b ^ 4 -
      a ^ 11 * b ^ 5 + a ^ 10 * b ^ 6 - a ^ 9 * b ^ 7 + a ^ 8 * b ^ 8 - a ^ 7 * b ^ 9 +
      a ^ 6 * b ^ 10 - a ^ 5 * b ^ 11 + a ^ 4 * b ^ 12 - a ^ 3 * b ^ 13 +
      a ^ 2 * b ^ 14 - a * b ^ 15 + b ^ 16) : ℤ) ∣ 17 := by
  set D := Int.gcd (a + b) (a ^ 16 - a ^ 15 * b + a ^ 14 * b ^ 2 - a ^ 13 * b ^ 3 +
      a ^ 12 * b ^ 4 - a ^ 11 * b ^ 5 + a ^ 10 * b ^ 6 - a ^ 9 * b ^ 7 + a ^ 8 * b ^ 8 -
      a ^ 7 * b ^ 9 + a ^ 6 * b ^ 10 - a ^ 5 * b ^ 11 + a ^ 4 * b ^ 12 - a ^ 3 * b ^ 13 +
      a ^ 2 * b ^ 14 - a * b ^ 15 + b ^ 16)
  have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 16 - a ^ 15 * b + a ^ 14 * b ^ 2 - a ^ 13 * b ^ 3 +
      a ^ 12 * b ^ 4 - a ^ 11 * b ^ 5 + a ^ 10 * b ^ 6 - a ^ 9 * b ^ 7 + a ^ 8 * b ^ 8 -
      a ^ 7 * b ^ 9 + a ^ 6 * b ^ 10 - a ^ 5 * b ^ 11 + a ^ 4 * b ^ 12 - a ^ 3 * b ^ 13 +
      a ^ 2 * b ^ 14 - a * b ^ 15 + b ^ 16) := Int.gcd_dvd_right _ _
  have hD_17b16 : (D : ℤ) ∣ 17 * b ^ 16 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 15 - 2 * a ^ 14 * b + 3 * a ^ 13 * b ^ 2 - 4 * a ^ 12 * b ^ 3 +
        5 * a ^ 11 * b ^ 4 - 6 * a ^ 10 * b ^ 5 + 7 * a ^ 9 * b ^ 6 - 8 * a ^ 8 * b ^ 7 +
        9 * a ^ 7 * b ^ 8 - 10 * a ^ 6 * b ^ 9 + 11 * a ^ 5 * b ^ 10 - 12 * a ^ 4 * b ^ 11 +
        13 * a ^ 3 * b ^ 12 - 14 * a ^ 2 * b ^ 13 + 15 * a * b ^ 14 - 16 * b ^ 15), by
      have key : 17 * b ^ 16 =
          (a ^ 16 - a ^ 15 * b + a ^ 14 * b ^ 2 - a ^ 13 * b ^ 3 + a ^ 12 * b ^ 4 -
          a ^ 11 * b ^ 5 + a ^ 10 * b ^ 6 - a ^ 9 * b ^ 7 + a ^ 8 * b ^ 8 - a ^ 7 * b ^ 9 +
          a ^ 6 * b ^ 10 - a ^ 5 * b ^ 11 + a ^ 4 * b ^ 12 - a ^ 3 * b ^ 13 +
          a ^ 2 * b ^ 14 - a * b ^ 15 + b ^ 16) -
          (a + b) * (a ^ 15 - 2 * a ^ 14 * b + 3 * a ^ 13 * b ^ 2 - 4 * a ^ 12 * b ^ 3 +
          5 * a ^ 11 * b ^ 4 - 6 * a ^ 10 * b ^ 5 + 7 * a ^ 9 * b ^ 6 - 8 * a ^ 8 * b ^ 7 +
          9 * a ^ 7 * b ^ 8 - 10 * a ^ 6 * b ^ 9 + 11 * a ^ 5 * b ^ 10 - 12 * a ^ 4 * b ^ 11 +
          13 * a ^ 3 * b ^ 12 - 14 * a ^ 2 * b ^ 13 + 15 * a * b ^ 14 - 16 * b ^ 15) := by ring
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
  have hcop_D_b16 : Nat.Coprime D (b ^ 16).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 16
  have hD_dvd_17b16_nat : D ∣ 17 * (b ^ 16).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_17b16
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b16.dvd_of_dvd_mul_right hD_dvd_17b16_nat
