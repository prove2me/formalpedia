-- Prove2me | solution 1 for lean_workbook_plus_4767
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:01:33.399584+00:00
-- url     : https://prove2.me/submissions/ccf3c272-5bdd-4e0a-bbef-ab15a3db1371

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum

theorem odd_modulus_obstruction (m n : ℕ) (hm : Odd m) (hn : Odd n)
    (hr : m % 3 = 2) : ¬ m ∣ 3 ^ n + 1 := by
  intro hd
  have hres : m % 12 = 5 ∨ m % 12 = 11 := by
    have := Nat.odd_iff.mp hm
    omega
  have hj : jacobiSym (-3 : ℤ) m = -1 := by
    rw [jacobiSym.mod_right (-3) hm]
    rcases hres with h | h <;> norm_num [h]
  have hz : (3 : ZMod m) ^ n = -1 := by
    have hh := (ZMod.natCast_eq_zero_iff (3 ^ n + 1) m).mpr hd
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hs : IsSquare (-3 : ZMod m) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨(3 : ZMod m) ^ (k + 1), ?_⟩
    rw [← pow_add, show k + 1 + (k + 1) = n + 1 by omega, pow_succ, hz]
    norm_num
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hj (by simpa using hs)

theorem prime_divisor_classification (n : ℕ) (hn : Odd n) (p : ℕ) :
    (p.Prime ∧ p % 3 = 2 ∧ p ∣ 3 ^ n + 1) ↔ p = 2 := by
  constructor
  · rintro ⟨hp, hr, hd⟩
    rcases hp.eq_two_or_odd with rfl | ho
    · rfl
    · exact False.elim (odd_modulus_obstruction p n (Nat.odd_iff.mpr ho) hn hr hd)
  · rintro rfl
    refine ⟨by decide, by decide, ?_⟩
    exact (((show Odd (3 : ℕ) from ⟨1, rfl⟩).pow).add_odd odd_one).two_dvd

theorem solution : ¬ (∀ n : ℕ, n % 2 = 1 →
    ¬ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ≡ 2 [ZMOD 3] ∧ p ∣ 3 ^ n + 1)) := by
  intro h
  have hp := (prime_divisor_classification 1 (by decide) 2).mpr rfl
  exact h 1 (by decide) ⟨2, hp.1, by decide, hp.2.2⟩
