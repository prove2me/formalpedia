-- Prove2me | solution 1 for lean_workbook_plus_7810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:58.957765+00:00
-- url     : https://prove2.me/submissions/1280cf13-2757-4bdf-bf33-0d20aafe1c3c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a + b + c + d = 1) :
  a * b + b * c + c * d ≤ 1 / 4 := by
  rcases h1 with ⟨ha,hb,hc,hd,hs⟩
  have had : 0 ≤ a*d := by positivity
  nlinarith [sq_nonneg (a+c-b-d),sq_nonneg (a+b+c+d-1)]
