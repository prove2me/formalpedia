-- Prove2me | solution 1 for lean_workbook_plus_30378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:08.577269+00:00
-- url     : https://prove2.me/submissions/e0cb6de3-0b0f-46db-8e9a-de01b7f27406

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b c : ℝ) (h : b > 0 ∧ c > 0) (hab : b * b + c * c = 1) : Real.sqrt (b * b + c * c) ≥ Real.sqrt 2 / 2 * (b + c) := by
  rw [hab,Real.sqrt_one]
  rcases h with ⟨hb,hc⟩
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hm := congrArg (fun t : ℝ => t*(b+c)^2) hs
  have hp : 0 ≤ Real.sqrt 2/2*(b+c) := by positivity
  nlinarith [sq_nonneg (b-c)]
