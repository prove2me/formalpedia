-- Prove2me | solution 1 for lean_workbook_plus_30891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:53.464813+00:00
-- url     : https://prove2.me/submissions/c60d9194-a0d4-4a72-9257-d461eb441948

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y : ℝ} : x ^ 4 + 6 * x ^ 2 * y ^ 2 + y ^ 4 ≥ 4 * x ^ 3 * y + 4 * x * y ^ 3 := by
  intros
  simp_all <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
