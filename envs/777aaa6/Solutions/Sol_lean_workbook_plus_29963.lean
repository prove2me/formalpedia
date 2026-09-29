-- Prove2me | solution 1 for lean_workbook_plus_29963
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:41.797411+00:00
-- url     : https://prove2.me/submissions/6fddb1e3-4f00-44f9-97c4-b933c33b8061

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) : x * y * z * (y * z ^ 2 + x ^ 2 * z + x * y ^ 2) + z ^ 4 * x ^ 2 + y ^ 2 * x ^ 4 + y ^ 4 * z ^ 2 ≥ 2 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2 := by
  intros
  have h : (0 : ℝ) ≤ (x * y * z * (y * z ^ 2 + x ^ 2 * z + x * y ^ 2) + z ^ 4 * x ^ 2 + y ^ 2 * x ^ 4 + y ^ 4 * z ^ 2) - (2 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2) := by
    calc
      0 ≤ ((1 / 6) : ℝ) * (((z * (y ^ 2)) + ((-1) * x * (z ^ 2))))^2 + ((1 / 6) : ℝ) * (((z * (y ^ 2)) + ((-1) * y * (x ^ 2))))^2 + ((1 / 6) : ℝ) * (((x * (z ^ 2)) + ((-1) * y * (x ^ 2))))^2 := by positivity
      _ = (x * y * z * (y * z ^ 2 + x ^ 2 * z + x * y ^ 2) + z ^ 4 * x ^ 2 + y ^ 2 * x ^ 4 + y ^ 4 * z ^ 2) - (2 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2) := by ring
  exact sub_nonneg.mp h
