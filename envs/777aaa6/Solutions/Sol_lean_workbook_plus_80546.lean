-- Prove2me | solution 1 for lean_workbook_plus_80546
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:52.514975+00:00
-- url     : https://prove2.me/submissions/795de380-7137-476c-9cfe-90713375ef70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (x y z : ℂ) (h₀ : x + y + z = 0) :
    2 * (x^5 + y^5 + z^5) = 5 * x * y * z * (x^2 + y^2 + z^2) := by
  have hz : z = -x - y := by linear_combination h₀
  rw [hz]
  ring
