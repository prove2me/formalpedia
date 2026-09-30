-- Prove2me | solution 1 for lean_workbook_plus_62528
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:52.779733+00:00
-- url     : https://prove2.me/submissions/2cda229d-5e75-49a2-b45a-f3331ec4d2d4

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (a : ℕ → ℝ) (ha : a 0 = 1)
    (hab : ∀ n, a (n + 1) = Real.sqrt (3 * a n + 1)) :
    ∃ M, ∀ n, a n < M := by
  refine ⟨4, ?_⟩
  intro n
  induction n with
  | zero => norm_num [ha]
  | succ n ih =>
    rw [hab]
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)).2
    linarith
