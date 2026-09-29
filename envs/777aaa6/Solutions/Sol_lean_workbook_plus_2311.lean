-- Prove2me | solution 1 for lean_workbook_plus_2311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:52.073066+00:00
-- url     : https://prove2.me/submissions/00aabe7e-7b1e-4cfb-8d34-b478ac93d37e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n ≥ 3, Real.sqrt (2 * n) ≥ Real.sqrt (n + Real.sqrt (2 * n + 1)) := by
  intro n hn
  apply Real.sqrt_le_sqrt
  have hs : Real.sqrt (2*n+1)≤n := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith [sq_nonneg (n-1)]
  linarith
