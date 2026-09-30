-- Prove2me | solution 1 for lean_workbook_plus_76955
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:45:28.842771+00:00
-- url     : https://prove2.me/submissions/e0933272-557b-4d9f-b76d-fc246197b034

import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : ¬ ∃ (a : ℤ), (a : ℝ)^2 = 6 := by
  have hi : Irrational (Real.sqrt 6) := by
    have hs : ¬ IsSquare (6 : ℕ) := by
      rintro ⟨n, hn⟩
      have hn3 : n < 3 := by nlinarith
      interval_cases n <;> norm_num at hn
    simpa using (irrational_sqrt_natCast_iff (n := 6)).2 hs
  rintro ⟨a, ha⟩
  apply hi.ne_int |a|
  rw [← ha, Real.sqrt_sq_eq_abs, Int.cast_abs]

#print axioms solution
