-- Prove2me | solution 1 for lean_workbook_plus_39652
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:39.477101+00:00
-- url     : https://prove2.me/submissions/8a87793f-b7c5-4d1c-9b34-1fb2c819f6a7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {x y t : ℝ} (h₁ : t = x + y) : (2 * (x + y) ^ 3 + 3 * x * y * (10 - x - y) = 2000) ↔ (2 * (t ^ 2 + 10 * t + 10 ^ 2) * (t - 10) = 3 * x * y * (t - 10)) := by
  intros
  grind
