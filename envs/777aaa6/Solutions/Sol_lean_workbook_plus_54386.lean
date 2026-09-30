-- Prove2me | solution 1 for lean_workbook_plus_54386
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:28:08.284474+00:00
-- url     : https://prove2.me/submissions/7f735bd0-2180-4b80-a3a6-0ebb4cb4c28d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace RadicalRecurrenceIntegrality

def pair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (5 * (pair n).1 + (pair n).2, 24 * (pair n).1 + 5 * (pair n).2)

theorem invariant (n : ℕ) : (pair n).2 ^ 2 = 24 * (pair n).1 ^ 2 + 1 := by
  induction n with
  | zero => norm_num [pair]
  | succ n ih =>
      change (24 * (pair n).1 + 5 * (pair n).2) ^ 2 =
        24 * (5 * (pair n).1 + (pair n).2) ^ 2 + 1
      nlinarith [ih]

theorem second_positive (n : ℕ) : 0 < (pair n).2 := by
  have hi := invariant n
  by_contra h
  have hy : (pair n).2 = 0 := Nat.eq_zero_of_not_pos h
  rw [hy] at hi
  nlinarith

theorem first_strictMono : StrictMono (fun n => (pair n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hy := second_positive n
  change (pair n).1 < 5 * (pair n).1 + (pair n).2
  omega

theorem sqrt_identity (n : ℕ) :
    Real.sqrt (24 * ((pair n).1 : ℝ) ^ 2 + 1) = ((pair n).2 : ℝ) := by
  have hi : ((pair n).2 : ℝ) ^ 2 = 24 * ((pair n).1 : ℝ) ^ 2 + 1 := by
    exact_mod_cast invariant n
  rw [← hi, Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

theorem real_recurrence (n : ℕ) :
    ((pair (n + 1)).1 : ℝ) =
      5 * ((pair n).1 : ℝ) + Real.sqrt (24 * ((pair n).1 : ℝ) ^ 2 + 1) := by
  rw [sqrt_identity]
  simp [pair]

theorem sequence_eq (x : ℕ → ℝ) (x0 : x 0 = 0)
    (hrec : ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n) ^ 2 + 1))
    (n : ℕ) : x n = ((pair n).1 : ℝ) := by
  induction n with
  | zero => simpa [pair] using x0
  | succ n ih => rw [hrec, ih, ← real_recurrence]

theorem full_sequence_properties (x : ℕ → ℝ) (x0 : x 0 = 0)
    (hrec : ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n) ^ 2 + 1)) :
    (∀ n, ∃ m : ℕ, x n = (m : ℝ)) ∧ StrictMono x := by
  constructor
  · intro n
    exact ⟨(pair n).1, sequence_eq x x0 hrec n⟩
  · intro i j hij
    rw [sequence_eq x x0 hrec i, sequence_eq x x0 hrec j]
    exact_mod_cast first_strictMono hij

end RadicalRecurrenceIntegrality

theorem solution (x : ℕ → ℝ) (x0 : x 0 = 0)
    (x_rec : ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n) ^ 2 + 1)) :
    ∀ n, 0 ≤ x n := by
  intro n
  rw [RadicalRecurrenceIntegrality.sequence_eq x x0 x_rec n]
  exact Nat.cast_nonneg _

#print axioms RadicalRecurrenceIntegrality.full_sequence_properties
