-- Prove2me | solution 1 for lean_workbook_plus_65981
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:26.591439+00:00
-- url     : https://prove2.me/submissions/e13bb735-18f3-4137-9fb7-b3ec4c071165

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    (a*b+b*c+c*a-1)^2 ≤ (a^2+1)*(b^2+1)*(c^2+1) := by
  nlinarith only [sq_nonneg (a*b*c-a-b-c)]
