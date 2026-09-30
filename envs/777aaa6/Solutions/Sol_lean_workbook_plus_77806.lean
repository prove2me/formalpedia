-- Prove2me | solution 1 for lean_workbook_plus_77806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:10.892743+00:00
-- url     : https://prove2.me/submissions/abf2e948-07ab-4455-bd78-7033d4f1bb64

import Mathlib.Analysis.Complex.Basic

theorem solution (q : ℚ) (q_pos : 0 < q) : ∃ m n : ℤ, q = m / n ∧ Int.gcd m n = 1 := by
  refine ⟨q.num, (q.den : ℤ), ?_, ?_⟩
  · rw [Int.cast_natCast, Rat.num_div_den]
  · rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact q.reduced
