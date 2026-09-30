-- Prove2me | solution 1 for lean_workbook_plus_51032
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:45:15.039623+00:00
-- url     : https://prove2.me/submissions/53bf0a69-4228-49f1-aa71-cfd7dfa2c59b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (h₁ : a > c) (h₂ : b > d)
    (h₃ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    Real.sqrt (a + b) - Real.sqrt c - Real.sqrt d >
      Real.sqrt (c + d) - Real.sqrt a - Real.sqrt b := by
  have hca : Real.sqrt c < Real.sqrt a := Real.sqrt_lt_sqrt (le_of_lt h₃.2.2.1) h₁
  have hdb : Real.sqrt d < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt h₃.2.2.2) h₂
  have hsum : Real.sqrt (c + d) < Real.sqrt (a + b) :=
    Real.sqrt_lt_sqrt (le_of_lt (add_pos h₃.2.2.1 h₃.2.2.2)) (by linarith)
  linarith

#print axioms solution
