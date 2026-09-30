-- Prove2me | solution 1 for lean_workbook_plus_67097
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:22.02264+00:00
-- url     : https://prove2.me/submissions/8d9e5635-a98c-4ba5-904e-ceaa0d57c301

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

theorem solution : ∀ a b c : ℂ,
    b ^ 2 - a * b + a ^ 2 / 4 = (b ^ 2 + c ^ 2) / 2 - a ^ 2 / 4 →
      c ^ 2 = (b - a) ^ 2 := by
  intro a b c h
  linear_combination -2 * h

#print axioms solution
