-- Prove2me | solution 1 for lean_workbook_plus_65845
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:36.108444+00:00
-- url     : https://prove2.me/submissions/38ca936f-fa50-4d5c-bf05-040ec7665a26

import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option autoImplicit false

lemma sqrt_three_irrational : Irrational (Real.sqrt 3) := by
  simpa using Nat.prime_three.irrational_sqrt

theorem solution : ¬ ∃ a : ℤ, (a : ℝ) ^ 2 = 3 := by
  rintro ⟨a, ha⟩
  have habs : Real.sqrt 3 = |(a : ℝ)| := by
    rw [← ha, Real.sqrt_sq_eq_abs]
  exact sqrt_three_irrational.ne_int |a| (by simpa only [Int.cast_abs] using habs)

#print axioms solution
