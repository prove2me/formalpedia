-- Prove2me | solution 1 for lean_workbook_plus_5799
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:31.128857+00:00
-- url     : https://prove2.me/submissions/7129bf38-d834-49ad-981d-c0a9a5ddc044

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum.NatFib

theorem solution (a : ℕ → ℚ) (a0 : a 0 = 0) (a1 : a 1 = 1) (a_rec : ∀ n, n ≥ 1 → a (n + 1) = a n + a (n - 1)) : ∃ A B : ℚ, (a 30 + a 29) / (a 26 + a 25) = A + B * Real.sqrt 5 ∧ A + B = 1346269 / 196418 := by
  have key : ∀ n, a n = (Nat.fib n : ℚ) ∧ a (n + 1) = (Nat.fib (n + 1) : ℚ) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [a0], by simp [a1]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [a_rec (k + 1) (by omega), Nat.add_sub_cancel, ih.1, ih.2, Nat.fib_add_two]
      push_cast
      ring
  have h30 : a 30 = (Nat.fib 30 : ℚ) := (key 30).1
  have h29 : a 29 = (Nat.fib 29 : ℚ) := (key 29).1
  have h26 : a 26 = (Nat.fib 26 : ℚ) := (key 26).1
  have h25 : a 25 = (Nat.fib 25 : ℚ) := (key 25).1
  refine ⟨1346269 / 196418, 0, ?_, by norm_num⟩
  rw [h30, h29, h26, h25]
  norm_num [Nat.fib]
