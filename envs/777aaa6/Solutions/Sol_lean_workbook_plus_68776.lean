-- Prove2me | solution 1 for lean_workbook_plus_68776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:22.335653+00:00
-- url     : https://prove2.me/submissions/fab7a39a-faed-429a-91fc-94044a314265

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2 := by
  intros
  have h : (0 : ℝ) ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2)) - ((x + y + z) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * ((z + ((-1) * y)))^2 + (1 : ℝ) * ((z + ((-1) * x)))^2 + (1 : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (3 * (x ^ 2 + y ^ 2 + z ^ 2)) - ((x + y + z) ^ 2) := by ring
  exact sub_nonneg.mp h
