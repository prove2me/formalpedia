-- Prove2me | solution 1 for lean_workbook_plus_81246
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:36:56.421779+00:00
-- url     : https://prove2.me/submissions/e755ae88-f062-4334-9dd3-ec66e6d4dd0a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) :
    (a^2+b^2+c^2)*(1/(b*c)+1/(c*a)+1/(a*b)) =
      a^2/(b*c)+b^2/(c*a)+c^2/(a*b)+a/b+b/a+b/c+c/b+c/a+a/c := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp_all <;> field_simp <;> ring
