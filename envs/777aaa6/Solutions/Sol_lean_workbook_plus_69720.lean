-- Prove2me | solution 1 for lean_workbook_plus_69720
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:35.205831+00:00
-- url     : https://prove2.me/submissions/7f8f71fe-60d4-46a1-a19f-319d7f2d63a3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (n : ℕ) (a : ℕ → ℕ)
    (h₀ : ∀ x, a (x + 1) = a x + 3 * x)
    (h₁ : a 1 = 69) (h₂ : 420 < a n) : 15 ≤ n := by
  have hzero : a 0 = 69 := by
    have h := h₀ 0
    simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h
    omega
  have formula : ∀ k, 2 * a k + 3 * k = 138 + 3 * k ^ 2 := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have he := h₀ k
      change 2 * a (k + 1) + 3 * (k + 1) = 138 + 3 * (k + 1) ^ 2
      rw [he]
      nlinarith
  have hn : 16 ≤ n := by
    by_contra hn
    have hn15 : n ≤ 15 := by omega
    have hsq : n ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left hn15 2
    have he := formula n
    nlinarith
  omega

#print axioms solution
