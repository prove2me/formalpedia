-- Prove2me | solution 1 for lean_workbook_plus_5314
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:26:19.102925+00:00
-- url     : https://prove2.me/submissions/1b092467-23b9-4886-9d31-fe585c2c1f4e

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

private lemma square_zero_binomial {R : Type*} [CommRing R] (a t : R)
    (ht : t ^ 2 = 0) (n : ℕ) (hn : 0 < n) :
    (a + t) ^ n = a ^ n + (n : R) * a ^ (n - 1) * t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ,
      Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [ih]
    linear_combination ((r : R) + 1) * a ^ r * ht

private lemma self_power_shift (k a : ℕ) (ha : Odd a) :
    Nat.ModEq (2 * 2 ^ (k + 1)) ((a + 2 ^ (k + 1)) ^ (a + 2 ^ (k + 1)))
      (a ^ a + 2 ^ (k + 1)) := by
  let t : ℕ := 2 ^ (k + 1)
  have ht : Even t := ⟨2 ^ k, by dsimp [t]; rw [pow_succ]; omega⟩
  have hm : 2 * t = 2 ^ (k + 2) := by dsimp [t]; ring
  have hnil : (t : ZMod (2 * t)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨2 ^ k, ?_⟩
    dsimp [t]
    rw [pow_succ]
    ring
  have htwo : (2 : ZMod (2 * t)) * t = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * t)
  have odd_half (b : ℕ) (hb : Odd b) : (b : ZMod (2 * t)) * t = t := by
    obtain ⟨j, rfl⟩ := hb
    push_cast
    linear_combination (j : ZMod (2 * t)) * htwo
  have hcop : a.Coprime (2 * t) := by
    rw [hm]
    exact ha.coprime_two_right.pow_right _
  have hphi : Nat.totient (2 * t) = t := by
    rw [hm]
    simpa [t] using Nat.totient_prime_pow_succ Nat.prime_two (k + 1)
  have heuler : (a : ZMod (2 * t)) ^ t = 1 := by
    have hc : Nat.ModEq (2 * t) (a ^ t) 1 := by
      simpa [hphi] using Nat.ModEq.pow_totient hcop
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (a ^ t) 1 (2 * t)).mpr hc
  have heodd : Odd (a + t) := ha.add_even ht
  have hcoefficient : ((a + t : ℕ) : ZMod (2 * t)) *
      (a : ZMod (2 * t)) ^ (a + t - 1) * t = t := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      odd_half ((a + t) * a ^ (a + t - 1)) (heodd.mul ha.pow)
  have hfinal : ((a : ZMod (2 * t)) + t) ^ (a + t) = (a : ZMod (2 * t)) ^ a + t := by
    rw [square_zero_binomial _ _ hnil _ heodd.pos]
    rw [hcoefficient, pow_add, heuler, mul_one]
  apply (ZMod.natCast_eq_natCast_iff _ _ (2 * t)).mp
  simpa only [t, Nat.cast_add, Nat.cast_pow] using hfinal

private lemma lift_choice (t x y : ℕ) (hle : y ≤ x) (hc : Nat.ModEq t x y) :
    Nat.ModEq (2 * t) x y ∨ Nat.ModEq (2 * t) (x + t) y := by
  obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hc.symm
  have hx : x = y + t * q := by omega
  rcases Nat.even_or_odd q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left
    have hxy : x = y + (2 * t) * r := by rw [hx]; ring
    rw [hxy]
    simp [Nat.ModEq, Nat.add_mod]
  · right
    have hxy : x + t = y + (2 * t) * (r + 1) := by rw [hx]; ring
    rw [hxy]
    simp [Nat.ModEq, Nat.add_mod]

private theorem representative_succ (k m : ℕ) (hm : Odd m) :
    ∃ n : ℕ, Odd n ∧ m ≤ n ∧ Nat.ModEq (2 ^ (k + 1)) (n ^ n) m := by
  induction k with
  | zero =>
    refine ⟨m, hm, le_rfl, ?_⟩
    change (m ^ m) % 2 = m % 2
    rw [Nat.odd_iff.mp hm.pow, Nat.odd_iff.mp hm]
  | succ k ih =>
    obtain ⟨a, ha, hma, hc⟩ := ih
    have hle : m ≤ a ^ a := hma.trans (Nat.le_self_pow ha.pos.ne' a)
    have hmod : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
    rcases lift_choice (2 ^ (k + 1)) (a ^ a) m hle hc with hstay | hshift
    · refine ⟨a, ha, hma, ?_⟩
      simpa only [Nat.succ_eq_add_one, hmod] using hstay
    · have ht : Even (2 ^ (k + 1)) := ⟨2 ^ k, by rw [pow_succ]; omega⟩
      refine ⟨a + 2 ^ (k + 1), ha.add_even ht, by omega, ?_⟩
      simpa only [Nat.succ_eq_add_one, hmod] using
        (self_power_shift k a ha).trans hshift

theorem odd_positive_representative (k m : ℕ) (hm : Odd m) :
    ∃ n : ℕ, Odd n ∧ m ≤ n ∧ Nat.ModEq (2 ^ k) (n ^ n) m := by
  cases k with
  | zero => exact ⟨m, hm, le_rfl, by simp only [pow_zero, Nat.ModEq, Nat.mod_one]⟩
  | succ k => exact representative_succ k m hm

theorem solution (k m : ℕ) (hm : Odd m) : ∃ n : ℕ, 2 ^ k ∣ n ^ n - m := by
  obtain ⟨n, hn, hmn, hc⟩ := odd_positive_representative k m hm
  exact ⟨n, (Nat.modEq_iff_dvd' (hmn.trans (Nat.le_self_pow hn.pos.ne' n))).mp hc.symm⟩
