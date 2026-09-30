-- Prove2me | solution 1 for lean_workbook_plus_43107
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:42:34.249265+00:00
-- url     : https://prove2.me/submissions/c097be44-eb01-44a0-a4f2-aaef4f2b8e1a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (h₁ : 1 ≤ a ∧ a ≤ 3) (h₂ : 1 ≤ b ∧ b ≤ 3)
    (h₃ : a + b = 4) : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt 3 - 1 := by
  have ha := Real.one_le_sqrt.mpr h₁.1
  have hb := Real.one_le_sqrt.mpr h₂.1
  have ha' := Real.sqrt_le_sqrt h₁.2
  have hb' := Real.sqrt_le_sqrt h₂.2
  rw [abs_le]
  constructor <;> linarith

#print axioms solution
