-- Prove2me | solution 1 for lean_workbook_plus_43185
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:04:18.314848+00:00
-- url     : https://prove2.me/submissions/eba0a2a8-bd09-4b17-b9a1-c33f8d1846d2

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

theorem odd_power_linear_relation {R : Type*} [CommRing R]
    (a b c : R) (hsq : a ^ 2 = b ^ 2) (hbase : a + c * b = 0)
    {n : ℕ} (hn : Odd n) : a ^ n + c * b ^ n = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, pow_add, pow_mul, pow_mul, pow_one, pow_one, hsq]
  linear_combination (b ^ 2) ^ k * hbase

theorem coefficient_1984_works (n : ℕ) (hn : Odd n) :
    (529 ^ n + 1984 * 132 ^ n) % 262417 = 0 := by
  have hsq : (529 : ZMod 262417) ^ 2 = (132 : ZMod 262417) ^ 2 := by decide
  have hbase : (529 : ZMod 262417) + 1984 * 132 = 0 := by decide
  have hz : ((529 ^ n + 1984 * 132 ^ n : ℕ) : ZMod 262417) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      odd_power_linear_relation (529 : ZMod 262417) 132 1984 hsq hbase hn
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hz)

theorem solution (m : ℕ) (hm : m > 0)
    (h : ∀ n : ℕ, Odd n → (529 ^ n + m * 132 ^ n) % 262417 = 0) :
    m ≥ 1984 := by
  have h1 := h 1 (by decide)
  simp only [pow_one] at h1
  omega

theorem coefficient_minimum :
    IsLeast {m : ℕ | 0 < m ∧
      ∀ n : ℕ, Odd n → (529 ^ n + m * 132 ^ n) % 262417 = 0} 1984 := by
  refine ⟨⟨by decide, coefficient_1984_works⟩, ?_⟩
  intro m hm
  exact solution m hm.1 hm.2

#print axioms solution
#print axioms odd_power_linear_relation
#print axioms coefficient_1984_works
#print axioms coefficient_minimum
