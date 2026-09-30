-- Prove2me | solution 1 for lean_workbook_plus_5612
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:49:02.811816+00:00
-- url     : https://prove2.me/submissions/6bdfb3c8-d7c2-4af3-8c5e-60fceb39fac8

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

namespace ConsecutivePower

theorem mixed_period (a b n : ℕ) (hn : 0 < n)
    (ha : a.Coprime n) (hb : b.Coprime n) :
    ∃ d : ℕ, 0 < d ∧ d ≤ n.totient ∧ d ∣ n.totient ∧
      (∀ k : ℕ, a ^ k ≡ b ^ k [MOD n] ↔ d ∣ k) ∧
      IsLeast {k : ℕ | 0 < k ∧ a ^ k ≡ b ^ k [MOD n]} d := by
  letI : NeZero n := ⟨hn.ne'⟩
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime a ha
  let v : (ZMod n)ˣ := ZMod.unitOfCoprime b hb
  let w := u * v⁻¹
  have hiff (k : ℕ) : a ^ k ≡ b ^ k [MOD n] ↔ w ^ k = 1 := by
    have hu : a ^ k ≡ b ^ k [MOD n] ↔ u ^ k = v ^ k := by
      rw [← ZMod.natCast_eq_natCast_iff]
      constructor
      · intro h
        apply Units.ext
        simpa [u, v] using h
      · intro h
        have hh := congrArg (fun z : (ZMod n)ˣ => (z : ZMod n)) h
        simpa [u, v] using hh
    rw [hu]
    simp only [w, mul_pow, inv_pow, mul_inv_eq_one]
  have hp : 0 < orderOf w := orderOf_pos w
  have hd : orderOf w ∣ n.totient := by
    simpa only [ZMod.card_units_eq_totient] using
      (orderOf_dvd_card : orderOf w ∣ Fintype.card (ZMod n)ˣ)
  have he (k : ℕ) : a ^ k ≡ b ^ k [MOD n] ↔ orderOf w ∣ k :=
    (hiff k).trans orderOf_dvd_iff_pow_eq_one.symm
  refine ⟨orderOf w, hp, Nat.le_of_dvd (Nat.totient_pos.mpr hn) hd, hd, he, ?_⟩
  exact ⟨⟨hp, (he _).mpr (dvd_refl _)⟩,
    fun k hk => Nat.le_of_dvd hk.1 ((he k).mp hk.2)⟩

theorem least_period_divides (a b n d k : ℕ) (hn : 0 < n)
    (ha : a.Coprime n) (hb : b.Coprime n)
    (hd : IsLeast {j : ℕ | 0 < j ∧ a ^ j ≡ b ^ j [MOD n]} d)
    (hk : a ^ k ≡ b ^ k [MOD n]) : d ∣ k := by
  obtain ⟨e, _, _, _, he, hm⟩ := mixed_period a b n hn ha hb
  rw [hd.unique hm]
  exact (he k).mp hk

theorem minFac_power_injective (n : ℕ) (hn : 1 < n) :
    Function.Injective (fun x : ZMod n.minFac => x ^ n) := by
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne'
  have hn0 : n ≠ 0 := by omega
  letI : Fact n.minFac.Prime := ⟨hp⟩
  have hc : n.Coprime (n.minFac - 1) :=
    Nat.coprime_of_lt_minFac (by have := hp.two_le; omega)
      (Nat.sub_lt hp.pos (by decide))
  have hcu : (Nat.card (ZMod n.minFac)ˣ).Coprime n := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hc.symm
  intro x y hxy
  by_cases hx : x = 0
  · subst x
    have hy : y = 0 := by simpa [hn0] using hxy.symm
    exact hy.symm
  by_cases hy : y = 0
  · subst y
    simpa [hn0] using hxy
  have hu : (Units.mk0 x hx) ^ n = (Units.mk0 y hy) ^ n := by
    apply Units.ext
    simpa using hxy
  have he := hcu.pow_left_bijective.injective hu
  exact congrArg (fun z : (ZMod n.minFac)ˣ => (z : ZMod n.minFac)) he

theorem minFac_dvd_difference (a b : ℤ) (n : ℕ) (hn : 1 < n)
    (h : (n : ℤ) ∣ a ^ n - b ^ n) : (n.minFac : ℤ) ∣ a - b := by
  have hd : (n.minFac : ℤ) ∣ (n : ℤ) := by exact_mod_cast Nat.minFac_dvd n
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ n - b ^ n) n.minFac).mpr
    (hd.trans h)
  have he : (a : ZMod n.minFac) ^ n = (b : ZMod n.minFac) ^ n := by
    simpa only [Int.cast_sub, Int.cast_pow, sub_eq_zero] using hz
  have he' := minFac_power_injective n hn he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) n.minFac).mp
  simpa only [Int.cast_sub, sub_eq_zero] using he'

theorem consecutive_int (a : ℤ) (n : ℕ) (hn : 1 < n) :
    ¬ (n : ℤ) ∣ (a + 1) ^ n - a ^ n := by
  intro h
  have hd := minFac_dvd_difference (a + 1) a n hn h
  have hd' : n.minFac ∣ 1 := by exact_mod_cast (by simpa using hd : (n.minFac : ℤ) ∣ 1)
  exact (Nat.minFac_prime hn.ne').not_dvd_one hd'

theorem consecutive_nat (a n : ℕ) (hn : 1 < n) :
    ¬ n ∣ (a + 1) ^ n - a ^ n := by
  intro h
  apply consecutive_int (a : ℤ) n hn
  have hle : a ^ n ≤ (a + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ a) n
  exact_mod_cast h

theorem three_two (n : ℕ) (hn : 1 < n) : ¬ n ∣ 3 ^ n - 2 ^ n :=
  consecutive_nat 2 n hn

theorem consecutive_nat_iff (a n : ℕ) : n ∣ (a + 1) ^ n - a ^ n ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    exact consecutive_nat a n (by omega) h
  · intro hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp

end ConsecutivePower

theorem solution (a b n : ℕ) (hab : a ≠ b) (hab2 : a ≠ 0 ∧ b ≠ 0)
    (hab3 : a * b * n ≠ 0) (hab4 : Nat.gcd a n = 1) (hab5 : Nat.gcd b n = 1) :
    ∃ t : ℕ, a ^ t ≡ b ^ t [ZMOD n] := by
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h => hab3 (by simp [h]))
  obtain ⟨d, _, _, _, he, _⟩ :=
    ConsecutivePower.mixed_period a b n hn hab4 hab5
  refine ⟨d, ?_⟩
  exact Int.natCast_modEq_iff.mpr ((he d).mpr (dvd_refl d))
