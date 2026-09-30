-- Prove2me | solution 1 for lean_workbook_plus_20026
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:07.816155+00:00
-- url     : https://prove2.me/submissions/27c1f81e-09c7-4772-8d80-ce133c5cad3a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace ConsecutivePowerSums

theorem power_le_next (n k : ℕ) (hk : 0 < k) : n ^ k ≤ n ^ (k + 1) := by
  by_cases hn : n = 0
  · simp [hn, ne_of_gt hk]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simpa [pow_succ] using Nat.mul_le_mul_left (n ^ k) hn1

theorem power_equality_iff (n k : ℕ) (hk : 0 < k) :
    n ^ k = n ^ (k + 1) ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hn) k)
      simpa [pow_succ] using h.symm
  · rintro (hn | hn) <;> simp [hn, ne_of_gt hk]

theorem sum_equality_iff {I : Type*} (s : Finset I) (a : I → ℕ)
    (k : ℕ) (hk : 0 < k) :
    (∑ i ∈ s, a i ^ (k + 1)) = (∑ i ∈ s, a i ^ k) ↔
      ∀ i ∈ s, a i = 0 ∨ a i = 1 := by
  classical
  have hle : ∀ i ∈ s, a i ^ k ≤ a i ^ (k + 1) :=
    fun i _ => power_le_next (a i) k hk
  constructor
  · intro h
    have heach := (Finset.sum_eq_sum_iff_of_le hle).1 h.symm
    exact fun i hi => (power_equality_iff (a i) k hk).1 (heach i hi)
  · intro h
    apply Finset.sum_congr rfl
    intro i hi
    exact ((power_equality_iff (a i) k hk).2 (h i hi)).symm

end ConsecutivePowerSums

theorem solution (x y : ℕ) (h₀ : 0 < x ∧ 0 < y)
    (h₁ : x ^ 3 + y ^ 3 = x ^ 2 + y ^ 2) : x = y ∧ x = 1 := by
  have hxle : x ^ 2 ≤ x ^ 3 := by
    simpa using ConsecutivePowerSums.power_le_next x 2 (by decide)
  have hyle : y ^ 2 ≤ y ^ 3 := by
    simpa using ConsecutivePowerSums.power_le_next y 2 (by decide)
  have hxEq : x ^ 2 = x ^ 3 := by omega
  have hyEq : y ^ 2 = y ^ 3 := by omega
  have hx1 : x = 1 := by
    rcases (ConsecutivePowerSums.power_equality_iff x 2 (by decide)).1 hxEq with h | h
    · omega
    · exact h
  have hy1 : y = 1 := by
    rcases (ConsecutivePowerSums.power_equality_iff y 2 (by decide)).1 hyEq with h | h
    · omega
    · exact h
  exact ⟨hx1.trans hy1.symm, hx1⟩
