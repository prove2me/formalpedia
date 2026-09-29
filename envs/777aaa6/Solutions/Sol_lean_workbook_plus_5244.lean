-- Prove2me | solution 1 for lean_workbook_plus_5244
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:09.94159+00:00
-- url     : https://prove2.me/submissions/4ea9a3ee-5d37-48ab-ba09-fc03654b5df3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (a - b) ^ 2 * (b - c) ^ 2 + 3 * (a * b * c - 1) ^ 2 + 3 - a * b * c ≥ 0 := by
  intros
  
  have h_identity : ((a - b) ^ 2 * (b - c) ^ 2 + 3 * (a * b * c - 1) ^ 2 + 3 - a * b * c) - (0) = (6 : ℝ) * 1 * ((1 + ((-7 / 12) * a * b * c)))^2 + (1 : ℝ) * 1 * ((((-1) * (b ^ 2)) + (a * b) + (b * c) + ((-1) * a * c)))^2 + ((23 / 24) : ℝ) * 1 * ((a * b * c))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a - b) ^ 2 * (b - c) ^ 2 + 3 * (a * b * c - 1) ^ 2 + 3 - a * b * c) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
