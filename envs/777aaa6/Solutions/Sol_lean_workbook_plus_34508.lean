-- Prove2me | solution 1 for lean_workbook_plus_34508
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:06.651071+00:00
-- url     : https://prove2.me/submissions/dab31186-0b2c-4b35-847a-067e50e2ebf0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℕ, n = 2 → Real.sqrt (1 / 5) < 1 / 2 ∧ 1 / 2 < Real.sqrt (1 / 3) := by
  intro n hn
  have h5 := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/5)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/3)
  have hs5 := Real.sqrt_nonneg ((1:ℝ)/5)
  have hs3 := Real.sqrt_nonneg ((1:ℝ)/3)
  constructor <;> nlinarith only [h5,h3,hs5,hs3]
