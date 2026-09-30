-- Prove2me | solution 1 for lean_workbook_plus_72948
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:14:27.85658+00:00
-- url     : https://prove2.me/submissions/f1581f44-bea6-4d2a-b528-aad5b5638143

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d : ℝ)
    (h1 : a ≥ c ∧ c ≥ 0 ∧ b ≥ d ∧ d ≥ 0)
    (h2 : 4 * a + 3 * d = 4 * b + 3 * c) :
    √(a * b) ≥ (c + d) / 2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]
