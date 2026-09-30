-- Prove2me | solution 1 for lean_workbook_plus_77681
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:45:20.455025+00:00
-- url     : https://prove2.me/submissions/fe39b47e-2867-4692-8a84-56c1acfec18d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2*(a+b+c)^6 - 12*(a+b+c)^4*(a*b+b*c+c*a) + 9*a*b*c*(a+b+c)^3 +
    27*(a+b+c)^2*(a*b+b*c+c*a)^2 + 243*a^2*b^2*c^2 +
    324*a*b*c*(a+b+c)*(a*b+b*c+c*a) ≥ 0 := by
  have hn : 0 ≤ 2*(a+b+c)^2*((a+b+c)^2-3*(a*b+b*c+c*a))^2 +
      9*(a+b+c)^2*(a*b+b*c+c*a)^2 + 9*(a*b*c)*(a+b+c)^3 +
      243*(a*b*c)^2 + 324*(a*b*c)*(a+b+c)*(a*b+b*c+c*a) := by positivity
  nlinarith only [hn]
