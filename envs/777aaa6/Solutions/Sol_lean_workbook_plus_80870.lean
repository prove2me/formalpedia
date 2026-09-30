-- Prove2me | solution 1 for lean_workbook_plus_80870
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:46:21.549539+00:00
-- url     : https://prove2.me/submissions/2c4eb4bc-a2e5-4280-8099-9e1b997cfe9c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a : ℕ → ℤ) (a1 : a 0 = 0) (a2 : a 1 = 1)
    (a_rec : ∀ n, a (4*n) = 1-a (n+1) ∧ a (4*n+2) = a (n+2) ∧ a (2*n+1) = a n) :
    ¬ ∃ n, 0 < n ∧ ∀ k, a k = a (k+n) := by
  have hbad := (a_rec 0).2.2
  norm_num [a1, a2] at hbad
