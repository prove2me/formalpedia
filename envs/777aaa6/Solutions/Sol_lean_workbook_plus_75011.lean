-- Prove2me | solution 1 for lean_workbook_plus_75011
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:18.196732+00:00
-- url     : https://prove2.me/submissions/190654b5-bac6-4076-bd1f-6124d9a8cfe3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (x + y) ^ 2 ≥ 4 * x * y ∧ (x + z) ^ 2 ≥ 4 * x * z ↔ (x - y) ^ 2 ≥ 0 ∧ (x - z) ^ 2 ≥ 0 := by
  intros
  grind
