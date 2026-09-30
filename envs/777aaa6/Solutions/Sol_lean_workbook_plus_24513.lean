-- Prove2me | solution 1 for lean_workbook_plus_24513
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:46:33.095725+00:00
-- url     : https://prove2.me/submissions/c9ad78a8-c621-48da-a8ce-d14016c553f6

import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ChebyshevDenominator

def numerator (t : ℚ) : ℤ := t.num ^ 3 - 3 * t.num * (t.den : ℤ) ^ 2

theorem numerator_coprime (t : ℚ) : IsCoprime (numerator t) (t.den : ℤ) := by
  have hc : IsCoprime t.num (t.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using t.reduced
  convert hc.pow_left (m := 3) |>.add_mul_right_left (-3 * t.num * (t.den : ℤ)) using 1
  dsimp [numerator]
  ring

theorem numerator_fraction (t : ℚ) :
    (numerator t : ℚ) / (t.den : ℚ) ^ 3 = t ^ 3 - 3 * t := by
  have hd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
  have hn : (t.num : ℚ) = t * t.den := (div_eq_iff hd).mp t.num_div_den
  dsimp [numerator]
  push_cast
  rw [hn]
  field_simp

theorem cleared_equation (p q : ℤ) (hq : q ≠ 0) (x : ℚ)
    (h : 4 * x ^ 3 - 3 * x = (p : ℚ) / q) :
    numerator (2 * x) * q = 2 * p * ((2 * x).den : ℤ) ^ 3 := by
  have hd : ((2 * x).den : ℚ) ^ 3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (2 * x).den_nz)
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hr : (numerator (2 * x) : ℚ) / ((2 * x).den : ℚ) ^ 3 = (2 * p : ℚ) / q := by
    rw [numerator_fraction]
    calc
      (2 * x) ^ 3 - 3 * (2 * x) = 2 * (4 * x ^ 3 - 3 * x) := by ring
      _ = 2 * ((p : ℚ) / q) := by rw [h]
      _ = (2 * p : ℚ) / q := by ring
  exact_mod_cast (div_eq_div_iff hd hq').mp hr

theorem denominator_factorization (p q : ℤ) (hq : q ≠ 0)
    (hpq : Nat.Coprime p.natAbs q.natAbs) (x : ℚ)
    (h : 4 * x ^ 3 - 3 * x = (p : ℚ) / q) :
    ∃ c : ℤ, q = ((2 * x).den : ℤ) ^ 3 * c ∧ c ∣ 2 ∧
      numerator (2 * x) * c = 2 * p := by
  let t := 2 * x
  have hc := cleared_equation p q hq x h
  have hcop := (numerator_coprime t).pow_right (n := 3)
  have hd : (t.den : ℤ) ^ 3 ∣ q := hcop.symm.dvd_of_dvd_mul_left (by
    rw [show numerator t * q = 2 * p * (t.den : ℤ) ^ 3 from hc]
    exact dvd_mul_left _ _)
  obtain ⟨c, hqc⟩ := hd
  have hv : (t.den : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast t.den_nz)
  have hcp : numerator t * c = 2 * p := by
    apply mul_left_cancel₀ hv
    calc
      (t.den : ℤ) ^ 3 * (numerator t * c) = numerator t * q := by rw [hqc]; ring
      _ = (t.den : ℤ) ^ 3 * (2 * p) := by rw [hc]; ring
  have hdq : c ∣ q := by rw [hqc]; exact dvd_mul_left _ _
  have hcop' : IsCoprime c p :=
    (Int.isCoprime_iff_nat_coprime.mpr hpq).symm.of_isCoprime_of_dvd_left hdq
  have hd2 : c ∣ 2 := hcop'.dvd_of_dvd_mul_right
    ⟨numerator t, by simpa only [mul_comm] using hcp.symm⟩
  exact ⟨c, hqc, hd2, hcp⟩

theorem integer_cubic_even (u : ℤ) : 2 ∣ u ^ 3 - 3 * u := by
  apply Int.dvd_of_emod_eq_zero
  have h : u % 2 = 0 ∨ u % 2 = 1 := by omega
  rcases h with h | h <;> norm_num [pow_succ, Int.sub_emod, Int.mul_emod, h]

theorem nontrivial_cube_divisor (p q : ℤ) (hq : q ≠ 0)
    (hpq : Nat.Coprime p.natAbs q.natAbs) (hqu : 1 < q.natAbs) (x : ℚ)
    (h : 4 * x ^ 3 - 3 * x = (p : ℚ) / q) :
    ∃ v : ℕ, 1 < v ∧ (v : ℤ) ^ 3 ∣ q := by
  obtain ⟨c, hqc, _, hc⟩ := denominator_factorization p q hq hpq x h
  refine ⟨(2 * x).den, ?_, ⟨c, hqc⟩⟩
  have hv := (2 * x).den_pos
  by_contra hh
  have he : (2 * x).den = 1 := by omega
  simp only [he, Nat.cast_one, one_pow, one_mul] at hqc
  subst c
  simp only [numerator, he, Nat.cast_one, one_pow, mul_one] at hc
  obtain ⟨d, hd⟩ := integer_cubic_even (2 * x).num
  rw [hd] at hc
  have hqp : q ∣ p := ⟨d, by nlinarith [hc]⟩
  have hu := (Int.isCoprime_iff_nat_coprime.mpr hpq).symm.isUnit_of_dvd hqp
  have := Int.isUnit_iff_natAbs_eq.mp hu
  omega

theorem unit_denominator_exception :
    (∃ x : ℚ, 4 * x ^ 3 - 3 * x = 1) ∧
      ¬ ∃ y : ℤ, 1 < y.natAbs ∧ y ^ 3 ∣ 1 := by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  rintro ⟨y, hy, hd⟩
  have hu := Int.isUnit_iff_natAbs_eq.mp (isUnit_of_dvd_one hd)
  simp only [Int.natAbs_pow] at hu
  have : 1 < y.natAbs ^ 3 := Nat.one_lt_pow (by decide) hy
  omega

end ChebyshevDenominator

theorem solution (p q : ℤ) (hq : q ≠ 0) (hpq : Nat.Coprime p.natAbs q.natAbs) :
    (∃ x : ℚ, 4 * x ^ 3 - 3 * x = p / q) → ∃ y : ℤ, y ^ 3 ∣ q := by
  rintro ⟨x, hx⟩
  by_cases hu : 1 < q.natAbs
  · obtain ⟨v, _, hv⟩ := ChebyshevDenominator.nontrivial_cube_divisor p q hq hpq hu x hx
    exact ⟨v, hv⟩
  · exact ⟨1, by simp⟩
