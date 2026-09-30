-- Prove2me | solution 1 for lean_workbook_plus_51878
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:11.746122+00:00
-- url     : https://prove2.me/submissions/77ea21ee-7694-4b5b-a164-0b2e06cfdb79

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem root_power_recurrence (z : ℂ) (hz : z ^ 2 = 4 * z - 5) (n : ℕ) :
    z ^ (n + 2) = 4 * z ^ (n + 1) - 5 * z ^ n := by
  rw [pow_add, hz, pow_succ]
  ring

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2)
    (a_rec : ∀ n, n > 1 → a n = 4 * a (n - 1) - 5 * a (n - 2)) :
    ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  have hz : (2 + Complex.I) ^ 2 = 4 * (2 + Complex.I) - 5 := by
    linear_combination Complex.I_sq
  have hr (n : ℕ) : ((2 + Complex.I) ^ (n + 2)).re =
      4 * ((2 + Complex.I) ^ (n + 1)).re - 5 * ((2 + Complex.I) ^ n).re := by
    simpa [Complex.mul_re] using congrArg Complex.re (root_power_recurrence _ hz n)
  refine ⟨fun n => ((2 + Complex.I) ^ n).re, ?_⟩
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using a0
  | one => simpa using a1
  | more n ih0 ih1 =>
      have ha := a_rec (n + 2) (by omega)
      rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at ha
      rw [ha, ih0, ih1]
      exact (hr n).symm

#print axioms solution
