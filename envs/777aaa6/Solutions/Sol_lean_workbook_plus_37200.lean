-- Prove2me | solution 1 for lean_workbook_plus_37200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:23.744718+00:00
-- url     : https://prove2.me/submissions/a013b05f-856d-492a-8d8c-7f117dabf739

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : 4 * x / (y + z) ≤ x * (1 / y + 1 / z) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
