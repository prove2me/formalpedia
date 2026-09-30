-- Prove2me | solution 1 for lean_workbook_plus_12307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:24.135522+00:00
-- url     : https://prove2.me/submissions/28b0be37-e80e-4154-8dc4-99b185b6b3c4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) (a : ℕ → ℝ) (a1 : a 0 = 3)
    (a_rec : ∀ n, a (n + 1) = Real.sqrt (2 + a n)) : ∀ n, a n > 2 := by
  intro k
  induction k with
  | zero => rw [a1]; norm_num
  | succ k ih =>
      rw [a_rec]
      have hs : Real.sqrt 4 < Real.sqrt (2 + a k) :=
        Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      norm_num at hs
      exact hs

#print axioms solution
