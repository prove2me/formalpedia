-- Prove2me | solution 1 for lean_workbook_plus_29744
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:56.725092+00:00
-- url     : https://prove2.me/submissions/cd814f42-ebfc-4e92-9887-dc0514ba348a

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

theorem prime_exponent_lt_prime_divisor (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p)
    (hdiv : p ∣ 2 ^ q - 1) : q < p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have htwo0 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hple := Nat.le_of_dvd (by decide : 0 < 2) hpdvd
    omega
  have htwo1 : (2 : ZMod p) ≠ 1 := by
    intro h
    have hbad : (1 : ZMod p) = 0 := by linear_combination h
    exact one_ne_zero hbad
  have hpow : (2 : ZMod p) ^ q = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (2 ^ q - 1) p).mpr hdiv
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))), Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  have horder : orderOf (2 : ZMod p) = q := orderOf_eq_prime hpow htwo1
  have hqdvd : q ∣ p - 1 := by
    rw [← horder]
    exact ZMod.orderOf_dvd_card_sub_one htwo0
  have hqle := Nat.le_of_dvd (by omega : 0 < p - 1) hqdvd
  omega

theorem corrected_statement (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) :
    ¬ (p ∣ 2 ^ q - 1 ∧ q ∣ 2 ^ p - 1) := by
  rintro ⟨h1, h2⟩
  have hqp := prime_exponent_lt_prime_divisor p q hp hq hp3 h1
  have hpq := prime_exponent_lt_prime_divisor q p hq hp hq3 h2
  omega

theorem solution :
    ¬ (∀ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≥ 5 ∧ q ≥ 5 →
      ¬ (p ∣ 2 ^ q - 1) ∧ ¬ (q ∣ 2 ^ p - 1)) := by
  intro h
  exact (h 31 5 (by decide)).1 (by decide)

#print axioms solution
#print axioms prime_exponent_lt_prime_divisor
#print axioms corrected_statement
