-- Prove2me | solution 1 for lean_workbook_plus_34510
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:35.029348+00:00
-- url     : https://prove2.me/submissions/424b9a5a-0af3-4dd6-9c30-24f7553dba0c

import Mathlib.Analysis.Complex.Basic

theorem solution {x y z : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + y + z) ^ 3 ≥ x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (y + z) * (z + x) := by
  have h : (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (y + z) * (z + x) := by ring
  exact h.ge
