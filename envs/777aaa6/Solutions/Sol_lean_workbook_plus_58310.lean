-- Prove2me | solution 1 for lean_workbook_plus_58310
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:28:38.852253+00:00
-- url     : https://prove2.me/submissions/e072a49f-c314-47e8-852a-976640a58b68

import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem consecutive_quadratic_gcd_square (k x y : ℕ) (hx : 0 < x) (_hy : 0 < y)
    (h : (k + 1) * x ^ 2 + x = k * y ^ 2 + y) :
    x < y ∧ y - x = (Nat.gcd x y) ^ 2 := by
  have hxy : x < y := by
    by_contra hn
    have hyx : y ≤ x := by omega
    have hs : y ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hyx 2
    have hk := Nat.mul_le_mul_left k hs
    nlinarith
  let d := y - x
  let e := k * (2 * x + d) + 1
  have hyd : y = x + d := by dsimp [d]; omega
  have hfac : x ^ 2 = d * e := by
    dsimp [e]
    rw [hyd] at h
    nlinarith
  have hcop : d.Coprime e := by
    apply Nat.coprime_of_dvd'
    intro p hp hpd hpe
    have hpx2 : p ∣ x ^ 2 := hpd.trans ⟨e, hfac⟩
    have hpx : p ∣ x := hp.dvd_of_dvd_pow hpx2
    have hsum : p ∣ 2 * x + d := Nat.dvd_add (dvd_mul_of_dvd_right hpx 2) hpd
    have hprod : p ∣ k * (2 * x + d) := dvd_mul_of_dvd_right hsum k
    exact (Nat.dvd_add_iff_right hprod).mpr hpe
  have hud : IsUnit (gcd d e) := by
    change IsUnit (Nat.gcd d e)
    rw [hcop.gcd_eq_one]
    exact isUnit_one
  have hue : IsUnit (gcd e d) := by
    change IsUnit (Nat.gcd e d)
    rw [hcop.symm.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ := exists_eq_pow_of_mul_eq_pow hud hfac.symm
  obtain ⟨s, hs⟩ := exists_eq_pow_of_mul_eq_pow hue (by simpa [Nat.mul_comm] using hfac.symm)
  have hxsq : x ^ 2 = (r * s) ^ 2 := by rw [hfac, hr, hs, mul_pow]
  have hxr : x = r * s := (Nat.pow_left_inj (by decide)).mp hxsq
  have hrs : r.Coprime s := by
    rw [hr, hs, Nat.coprime_pow_left_iff (by decide), Nat.coprime_pow_right_iff (by decide)] at hcop
    exact hcop
  have hg : Nat.gcd x y = r := by
    rw [← Nat.gcd_sub_self_right (Nat.le_of_lt hxy)]
    change Nat.gcd x d = r
    rw [hxr, hr, pow_two, Nat.gcd_mul_left, hrs.symm.gcd_eq_one, Nat.mul_one]
  exact ⟨hxy, by change d = _; rw [hr, hg]⟩

theorem consecutive_quadratic_reverse_not_square (k x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : (k + 1) * x ^ 2 + x = k * y ^ 2 + y) :
    ∀ z : ℤ, z ^ 2 ≠ (x : ℤ) - (y : ℤ) := by
  have hxy := (consecutive_quadratic_gcd_square k x y hx hy h).1
  have hxy' : (x : ℤ) < y := by exact_mod_cast hxy
  intro z hz
  nlinarith [sq_nonneg z]

theorem four_three_positive_witness :
    4 * (26 : ℕ) ^ 2 + 26 = 3 * 30 ^ 2 + 30 ∧
      30 - 26 = (Nat.gcd 26 30) ^ 2 ∧ (30 : ℕ) - 26 = 4 := by
  decide

theorem solution (x y : ℕ) (h : 0 < x ∧ 0 < y)
    (hxy : 4 * x ^ 2 + x = 3 * y ^ 2 + y) : ∃ h : ℕ, h ^ 2 = x - y := by
  obtain ⟨horder, _⟩ := consecutive_quadratic_gcd_square 3 x y h.1 h.2 hxy
  exact ⟨0, by rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt horder)]; norm_num⟩
