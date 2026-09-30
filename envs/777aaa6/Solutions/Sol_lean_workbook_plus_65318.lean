-- Prove2me | solution 1 for lean_workbook_plus_65318
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:01.390149+00:00
-- url     : https://prove2.me/submissions/4778598c-f953-440c-bdd0-14abe4daeab8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ (a : ℕ → NNReal), 0 < a 0 →
    (∀ n, a (n + 1) = Real.sqrt (a n - 1 / a n)) → False) := by
  intro h
  let a : ℕ → NNReal := fun n => if n = 0 then 1 else 0
  apply h a (by simp [a])
  intro n
  cases n <;> norm_num [a]

#print axioms solution
