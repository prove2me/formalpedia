-- Prove2me | solution 1 for lean_workbook_plus_34922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:25.629714+00:00
-- url     : https://prove2.me/submissions/95f3a12f-f5f6-4465-be3a-00e5db2f80c2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x ↔ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≥ 0 := by
  intros
  grind
