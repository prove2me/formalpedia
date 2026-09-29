-- Prove2me | solution 1 for lean_workbook_plus_41501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:53.31371+00:00
-- url     : https://prove2.me/submissions/2ec4e2b6-5596-4758-97fb-8a6e34f146bc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a^4 + b^4 + 2 ≥ 4 * a * b := by
  nlinarith [sq_nonneg (a^2-b^2),sq_nonneg (a*b-1)]
