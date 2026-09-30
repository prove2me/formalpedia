-- Prove2me | solution 1 for lean_workbook_plus_80056
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:11.226372+00:00
-- url     : https://prove2.me/submissions/1356e3b5-1196-4c10-a6f9-225a1492aae9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 - a / (1 + a + a * b) - b / (1 + b + b * c) - c / (1 + c + c * a) : ℝ) =
      (a * b * c - 1) ^ 2 /
        ((1 + a + a * b) * (1 + b + b * c) * (1 + c + c * a)) := by
  have h₁ : 1 + a + a * b ≠ 0 := ne_of_gt (by positivity)
  have h₂ : 1 + b + b * c ≠ 0 := ne_of_gt (by positivity)
  have h₃ : 1 + c + c * a ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

#print axioms solution
