-- Prove2me | solution 1 for lean_workbook_plus_42161
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:11:43.895329+00:00
-- url     : https://prove2.me/submissions/02c6429b-4c99-4d19-976b-dc4c0d7622ec

import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

theorem coprime_power_period (q b : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hcop : Nat.Coprime q b) :
    ∃ d : ℕ, 0 < d ∧ d ≤ q.totient ∧ d ∣ q.totient ∧
      (∀ n : ℕ, q ∣ b ^ n - 1 ↔ d ∣ n) ∧
      IsLeast {n : ℕ | 0 < n ∧ q ∣ b ^ n - 1} d := by
  letI : NeZero q := ⟨hq.ne'⟩
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime b hcop.symm
  have hiff (n : ℕ) : q ∣ b ^ n - 1 ↔ u ^ n = 1 := by
    have hpow : 1 ≤ b ^ n := Nat.one_le_pow n b hb
    have hcast : ((b ^ n - 1 : ℕ) : ZMod q) = (b : ZMod q) ^ n - 1 := by
      rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
    constructor
    · intro hd
      apply Units.ext
      have hz := (ZMod.natCast_eq_zero_iff _ q).mpr hd
      rw [hcast, sub_eq_zero] at hz
      simpa [u] using hz
    · intro h
      apply (ZMod.natCast_eq_zero_iff _ q).mp
      rw [hcast, sub_eq_zero]
      have hh := congrArg (fun x : (ZMod q)ˣ => (x : ZMod q)) h
      simpa [u] using hh
  have hpos : 0 < orderOf u := orderOf_pos u
  have hle : orderOf u ≤ q.totient := by
    simpa only [ZMod.card_units_eq_totient] using
      (orderOf_le_card_univ : orderOf u ≤ Fintype.card (ZMod q)ˣ)
  have hdvd : orderOf u ∣ q.totient := by
    simpa only [ZMod.card_units_eq_totient] using
      (orderOf_dvd_card : orderOf u ∣ Fintype.card (ZMod q)ˣ)
  have hall (n : ℕ) : q ∣ b ^ n - 1 ↔ orderOf u ∣ n :=
    (hiff n).trans orderOf_dvd_iff_pow_eq_one.symm
  refine ⟨orderOf u, hpos, hle, hdvd, hall, ?_⟩
  exact ⟨⟨hpos, (hall _).mpr (dvd_refl _)⟩,
    fun n hn => Nat.le_of_dvd hn.1 ((hall n).mp hn.2)⟩

theorem positive_decimal_exponent (q : ℕ) (hq : Nat.Coprime q 10) :
    ∃ n : ℕ, 0 < n ∧ n ≤ q.totient ∧ q ∣ 10 ^ n - 1 := by
  have hq0 : 0 < q := by
    by_contra h
    have : q = 0 := by omega
    subst q
    norm_num at hq
  obtain ⟨d, hd, hle, _, hall, _⟩ := coprime_power_period q 10 hq0 (by decide) hq
  exact ⟨d, hd, hle, (hall d).mpr (dvd_refl d)⟩

theorem solution (q : ℕ) (hq : Nat.Coprime q 10) : ∃ n : ℕ, q ∣ 10 ^ n - 1 := by
  obtain ⟨n, _, _, hn⟩ := positive_decimal_exponent q hq
  exact ⟨n, hn⟩
