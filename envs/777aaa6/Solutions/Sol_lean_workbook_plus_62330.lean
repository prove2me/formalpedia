-- Prove2me | solution 1 for lean_workbook_plus_62330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:39.76756+00:00
-- url     : https://prove2.me/submissions/2a0c8226-4198-43a1-8fbd-528e63361bfb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option autoImplicit false

lemma scaled_recurrence_is_fibonacci (p : ℕ → ℚ) (h₀ : p 0 = 1) (h₁ : p 1 = 1)
    (h₂ : ∀ x, p (x + 2) = 1 / 2 * p (x + 1) + 1 / 4 * p x)
    (n : ℕ) : (2 : ℚ) ^ n * p n = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [h₀, Nat.fib_add_two]
  | one => norm_num [h₁, Nat.fib_add_two]
  | more n ih₀ ih₁ =>
    calc
      (2 : ℚ) ^ (n + 2) * p (n + 2) =
          (2 : ℚ) ^ n * p n + (2 : ℚ) ^ (n + 1) * p (n + 1) := by
        rw [h₂]
        simp only [pow_succ]
        ring
      _ = (Nat.fib (n + 2) : ℚ) + Nat.fib (n + 1 + 2) := by rw [ih₀, ih₁]
      _ = Nat.fib (n + 2 + 2) := by
        exact_mod_cast (Nat.fib_add_two (n := n + 2)).symm

theorem solution (p : ℕ → ℚ) (h₀ : p 0 = 1) (h₁ : p 1 = 1)
    (h₂ : ∀ x, p (x + 2) = 1 / 2 * p (x + 1) + 1 / 4 * p x) :
    p 6 = 21 / 64 := by
  have h := scaled_recurrence_is_fibonacci p h₀ h₁ h₂ 6
  norm_num [Nat.fib_add_two] at h
  linarith

#print axioms solution
