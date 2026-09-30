-- Prove2me | solution 1 for lean_workbook_plus_81176
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:46:23.551701+00:00
-- url     : https://prove2.me/submissions/2f9e4da3-32f5-4671-8970-3771e3a89148

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (n : ℕ) (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 41)
    (a_rec : ∀ n, a (n+1) = 3*a (n-1) + Real.sqrt (8*(a n^2 + a (n-1)^2))) :
    ∀ n, a n = ⌊a n⌋ := by
  have hroot : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hbad := a_rec 0
  norm_num [a0, a1, hroot] at hbad
