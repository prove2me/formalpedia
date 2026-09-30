-- Prove2me | solution 1 for lean_workbook_plus_9012
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:03:46.482353+00:00
-- url     : https://prove2.me/submissions/d2c50f8b-1c34-4d7c-a4c1-72d6a784459a

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace LucasPrimeCongruence

def state : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n + 1 => ((state n).2, (state n).1 + (state n).2)

def lucas (n : ℕ) : ℕ := (state n).1

theorem lucas_zero : lucas 0 = 2 := rfl

theorem lucas_one : lucas 1 = 1 := rfl

theorem lucas_recurrence (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := by
  change (state n).1 + (state n).2 = (state n).2 + (state n).1
  omega

theorem unique (a : ℕ → ℕ) (h0 : a 0 = 2) (h1 : a 1 = 1)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) : ∀ n, a n = lucas n := by
  apply Nat.twoStepInduction
  · exact h0
  · exact h1
  · intro n hn hn1
    rw [hr, lucas_recurrence, hn, hn1]

theorem source_iff (a : ℕ → ℕ) :
    (a 0 = 2 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) = a (n + 1) + a n) ↔ a = lucas := by
  constructor
  · rintro ⟨h0, h1, hr⟩
    exact funext (unique a h0 h1 hr)
  · rintro rfl
    exact ⟨lucas_zero, lucas_one, lucas_recurrence⟩

theorem source_exists : ∃ a : ℕ → ℕ,
    a 0 = 2 ∧ a 1 = 1 ∧ ∀ n, a (n + 2) = a (n + 1) + a n :=
  ⟨lucas, lucas_zero, lucas_one, lucas_recurrence⟩

theorem positive (a : ℕ → ℕ) (h0 : a 0 = 2) (h1 : a 1 = 1)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) : ∀ n, 0 < a n := by
  apply Nat.twoStepInduction
  · omega
  · omega
  · intro n hn hn1
    rw [hr]
    omega

theorem two_le_even (a : ℕ → ℕ) (h0 : a 0 = 2)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) (m : ℕ) : 2 ≤ a (2 * m) := by
  induction m with
  | zero => simpa only [Nat.mul_zero, h0] using (le_refl (2 : ℕ))
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, hr]
      omega

theorem even_norm {R : Type*} [CommRing R] (a : ℕ → R)
    (h0 : a 0 = 2) (h1 : a 1 = 1)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) (m : ℕ) :
    a (2 * m + 1) ^ 2 - a (2 * m) * a (2 * m + 1) - a (2 * m) ^ 2 = -5 := by
  induction m with
  | zero =>
      simp only [Nat.mul_zero, zero_add, h0, h1]
      ring
  | succ m ih =>
      have h2 : a (2 * (m + 1)) = a (2 * m) + a (2 * m + 1) := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, hr]
        ring
      have h3 : a (2 * (m + 1) + 1) = a (2 * m) + 2 * a (2 * m + 1) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, hr,
          show 2 * m + 1 + 1 = 2 * m + 2 by omega, hr]
        ring
      rw [h2, h3]
      calc
        _ = a (2 * m + 1) ^ 2 - a (2 * m) * a (2 * m + 1) - a (2 * m) ^ 2 := by ring
        _ = -5 := ih

theorem next_eq_one {R : Type*} [CommRing R] [NoZeroDivisors R] (a : ℕ → R)
    (h0 : a 0 = 2) (h1 : a 1 = 1)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) (m : ℕ)
    (he : a (2 * m) = 2) : a (2 * m + 1) = 1 := by
  have hn := even_norm a h0 h1 hr m
  rw [he] at hn
  have hs : (a (2 * m + 1) - 1) ^ 2 = 0 := by linear_combination hn
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)

theorem prime_same_index (p : ℕ) (hp : p.Prime) (a : ℕ → ℕ)
    (h0 : a 0 = 2) (h1 : a 1 = 1)
    (hr : ∀ n, a (n + 2) = a (n + 1) + a n) (m : ℕ)
    (hm : p ∣ a (2 * m) - 2) : p ∣ a (2 * m + 1) - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have he0 : ((a (2 * m) - 2 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hm
  have he : (a (2 * m) : ZMod p) = 2 := by
    rw [Nat.cast_sub (two_le_even a h0 hr m), Nat.cast_ofNat] at he0
    exact sub_eq_zero.mp he0
  have hn : (a (2 * m + 1) : ZMod p) = 1 :=
    next_eq_one (fun n => (a n : ZMod p))
      (by dsimp only; rw [h0]; rfl) (by dsimp only; rw [h1, Nat.cast_one])
      (fun n => by dsimp only; rw [hr, Nat.cast_add]) m he
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sub (positive a h0 h1 hr _), Nat.cast_one, hn, sub_self]

theorem lucas_prime_same_index (p : ℕ) (hp : p.Prime) (m : ℕ)
    (hm : p ∣ lucas (2 * m) - 2) : p ∣ lucas (2 * m + 1) - 1 :=
  prime_same_index p hp lucas lucas_zero lucas_one lucas_recurrence m hm

theorem composite_failure : 8 ∣ lucas 6 - 2 ∧ ¬ 8 ∣ lucas 7 - 1 := by
  decide

end LucasPrimeCongruence

theorem solution (p : ℕ) (hp : p.Prime) (a : ℕ → ℕ)
    (h1 : a 0 = 2) (h2 : a 1 = 1)
    (h3 : ∀ n, a (n + 2) = a (n + 1) + a n)
    (h4 : ∃ m, p ∣ a (2 * m) - 2) : ∃ m, p ∣ a (2 * m + 1) - 1 := by
  obtain ⟨m, hm⟩ := h4
  exact ⟨m, LucasPrimeCongruence.prime_same_index p hp a h1 h2 h3 m hm⟩

#print axioms LucasPrimeCongruence.state
#print axioms LucasPrimeCongruence.lucas
#print axioms LucasPrimeCongruence.lucas_zero
#print axioms LucasPrimeCongruence.lucas_one
#print axioms LucasPrimeCongruence.lucas_recurrence
#print axioms LucasPrimeCongruence.unique
#print axioms LucasPrimeCongruence.source_iff
#print axioms LucasPrimeCongruence.source_exists
#print axioms LucasPrimeCongruence.positive
#print axioms LucasPrimeCongruence.two_le_even
#print axioms LucasPrimeCongruence.even_norm
#print axioms LucasPrimeCongruence.next_eq_one
#print axioms LucasPrimeCongruence.prime_same_index
#print axioms LucasPrimeCongruence.lucas_prime_same_index
#print axioms LucasPrimeCongruence.composite_failure
#print axioms solution
