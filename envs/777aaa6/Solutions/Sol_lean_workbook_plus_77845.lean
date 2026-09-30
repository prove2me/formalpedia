-- Prove2me | solution 1 for lean_workbook_plus_77845
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:16.449651+00:00
-- url     : https://prove2.me/submissions/cad4fae9-eab6-4021-8eb6-e3065c96a251

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : P = fun x : ℝ => x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d) :
    P 1 = 10 ∧ P 2 = 20 ∧ P 3 = 30 → (P 12 + P (-8)) / 10 = 1984 := by
  subst P
  rintro ⟨h1, h2, h3⟩
  linear_combination 10 * h1 - (99 / 5) * h2 + 10 * h3

#print axioms solution
