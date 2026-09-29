-- Prove2me | solution 1 for lean_workbook_plus_47216
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:19.339239+00:00
-- url     : https://prove2.me/submissions/3494d401-7f6c-42a0-b349-7940277b91f8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z a b : ℝ) : (x - a) * (y - b) * (z - b) ≥ 0 ↔ x * y * z + x * b ^ 2 + a * b * (y + z) ≥ a * b ^ 2 + a * y * z + b * (x * y + x * z) := by
  intros
  grind
