-- Prove2me | solution 1 for lean_workbook_plus_43939
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:02.697479+00:00
-- url     : https://prove2.me/submissions/027934aa-3130-4ab2-b717-c4346d12f02d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a * b + b * c + c * a - 1) ^ 2 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
  intro a b c
  nlinarith only [sq_nonneg (a*b*c-a-b-c)]
