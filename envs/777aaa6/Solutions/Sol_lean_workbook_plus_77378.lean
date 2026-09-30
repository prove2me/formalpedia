-- Prove2me | solution 1 for lean_workbook_plus_77378
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:13.850177+00:00
-- url     : https://prove2.me/submissions/b1c683b1-2fc6-4779-b5ed-de8987bfcc53

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (x y z : ℤ) (p s : ℤ)
    (h₁ : x = 6 * p ^ 2 - 4 * p * s + s ^ 2)
    (h₂ : y = 6 * p ^ 2 - s ^ 2)
    (h₃ : z = 6 * p ^ 2 - 6 * p * s + s ^ 2) :
    3 * x ^ 2 - y ^ 2 = 2 * z ^ 2 := by
  rw [h₁, h₂, h₃]
  ring

#print axioms solution
