-- Prove2me | solution 1 for lean_workbook_plus_16214
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:54:18.637215+00:00
-- url     : https://prove2.me/submissions/491ce36b-7afa-449f-b3ea-95c3e7c367fc

import Mathlib

namespace TwoSidedFixedPointPowers

theorem power_fixed {M : Type*} [Monoid M] {a b c : M}
    (h : a * c * b = c) (n : ℕ) : a ^ n * c * b ^ n = c := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      a ^ (n + 1) * c * b ^ (n + 1) = a * (a ^ n * c * b ^ n) * b := by
        rw [pow_succ' a n, pow_succ b n]
        simp only [mul_assoc]
      _ = a * c * b := by rw [ih]
      _ = c := h

theorem fixed_iff {M : Type*} [Monoid M] (a b c : M) :
    a * c * b = c ↔ ∀ n : ℕ, a ^ n * c * b ^ n = c := by
  constructor
  · exact fun h n => power_fixed h n
  · intro h
    simpa using h 1

theorem power_absorption {M : Type*} [Monoid M] {a b : M}
    (h : a * b ^ 2 = b) (n : ℕ) : a ^ n * b ^ (n + 1) = b := by
  have hf : a * b * b = b := by simpa only [pow_two, mul_assoc] using h
  calc
    a ^ n * b ^ (n + 1) = a ^ n * b * b ^ n := by
      rw [pow_succ' b n, mul_assoc]
    _ = b := power_fixed hf n

theorem power_absorption_iff {M : Type*} [Monoid M] (a b : M) :
    a * b ^ 2 = b ↔ ∀ n : ℕ, a ^ n * b ^ (n + 1) = b := by
  constructor
  · exact fun h n => power_absorption h n
  · intro h
    simpa using h 1

theorem natural_premise (a b : ℕ) :
    a * b ^ 2 = b ↔ b = 0 ∨ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      have hab : a * b = 1 := mul_right_cancel₀ hb
        (show a * b * b = 1 * b by simpa only [pow_two, mul_assoc, one_mul] using h)
      exact ⟨Nat.eq_one_of_mul_eq_one_right hab, Nat.eq_one_of_mul_eq_one_left hab⟩
  · rintro (rfl | ⟨rfl, rfl⟩) <;> simp

theorem natural_power_classification (a b : ℕ) :
    (∀ n : ℕ, a ^ n * b ^ (n + 1) = b) ↔ b = 0 ∨ a = 1 ∧ b = 1 := by
  rw [← power_absorption_iff, natural_premise]

theorem noncommuting_example :
    ∃ a b c : Function.End ℕ, a * c * b = c ∧ a * b ≠ b * a := by
  refine ⟨fun _ => 0, fun n => n + 1, fun _ => 0, rfl, ?_⟩
  intro h
  have hh := congrFun h 0
  change (0 : ℕ) = 1 at hh
  norm_num at hh

end TwoSidedFixedPointPowers

theorem solution (a b : ℕ) (h : a * b ^ 2 = b) :
    ∀ k : ℕ, a ^ k * b ^ (k + 1) = b :=
  TwoSidedFixedPointPowers.power_absorption h

#print axioms TwoSidedFixedPointPowers.power_fixed
#print axioms TwoSidedFixedPointPowers.fixed_iff
#print axioms TwoSidedFixedPointPowers.power_absorption
#print axioms TwoSidedFixedPointPowers.power_absorption_iff
#print axioms TwoSidedFixedPointPowers.natural_premise
#print axioms TwoSidedFixedPointPowers.natural_power_classification
#print axioms TwoSidedFixedPointPowers.noncommuting_example
#print axioms solution
