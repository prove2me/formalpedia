-- Prove2me | solution 1 for lean_workbook_plus_34510
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:49.023952+00:00
-- url     : https://prove2.me/submissions/4d29b12f-7b3c-4363-b1d5-609f17936a70

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y z : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + y + z) ^ 3 ≥ x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (y + z) * (z + x) := by
  (intros; linarith)
