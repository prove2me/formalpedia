-- Prove2me | solution 1 for lean_workbook_plus_8873
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:39.220058+00:00
-- url     : https://prove2.me/submissions/e1df3d7f-6702-46af-8f2c-b1509106eddd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (ε : ℝ) (hε : 0 < ε) : ∃ n : ℤ, (1 : ℝ) / n < ε := by
  rcases exists_nat_one_div_lt hε with ⟨n,hn⟩
  refine ⟨(n:ℤ)+1,?_⟩
  simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hn
