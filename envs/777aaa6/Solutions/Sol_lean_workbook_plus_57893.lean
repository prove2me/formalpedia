-- Prove2me | solution 1 for lean_workbook_plus_57893
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:06.452369+00:00
-- url     : https://prove2.me/submissions/8bdd01d3-53e5-4871-a46c-c53931fc6457

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : z ^ 4 * x ^ 2 + x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 ≥ 1 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2 := by
  intros
  have h : (0 : ℝ) ≤ (z ^ 4 * x ^ 2 + x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2) - (1 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * (z ^ 2))))^2 + ((1 / 3) : ℝ) * (((z * (y ^ 2)) + ((-1) * y * (x ^ 2))))^2 + ((1 / 3) : ℝ) * (((x * (z ^ 2)) + ((-1) * y * (x ^ 2))))^2 := by positivity
      _ = (z ^ 4 * x ^ 2 + x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2) - (1 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2) := by ring
  exact sub_nonneg.mp h
