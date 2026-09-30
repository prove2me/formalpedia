-- Prove2me | solution 1 for lean_workbook_plus_54602
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:07:28.309882+00:00
-- url     : https://prove2.me/submissions/b57696ff-90bd-486d-945f-a130022f87f6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 3)
    (a_rec : ∀ n, a (n + 1) = a n ^ 2 - 2) :
    ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  let r : ℝ := (3 + Real.sqrt 5) / 2
  let s : ℝ := (3 - Real.sqrt 5) / 2
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hrs : r * s = 1 := by dsimp [r, s]; nlinarith
  have hclosed (n : ℕ) : (a n : ℝ) = r ^ (2 ^ n) + s ^ (2 ^ n) := by
    induction n with
    | zero =>
        rw [a0]
        norm_num only [pow_zero, pow_one, Int.cast_ofNat]
        dsimp [r, s]
        ring
    | succ n ih =>
        have hm : r ^ (2 ^ n) * s ^ (2 ^ n) = 1 := by
          rw [← mul_pow, hrs, one_pow]
        rw [a_rec]
        push_cast
        rw [ih, show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n, pow_mul, pow_mul]
        nlinarith only [hm]
  refine ⟨fun n => ⌊r ^ (2 ^ n) + s ^ (2 ^ n)⌋, ?_⟩
  intro n
  dsimp only
  rw [← hclosed n]
  simp

#print axioms solution
