-- Prove2me | solution 1 for lean_workbook_plus_16326
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:20.342005+00:00
-- url     : https://prove2.me/submissions/d34b694a-9ca3-48c5-a34c-843e164573ac

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (t : ℝ), (118 / 7 * t ^ 4 + 8 * t ^ 3 + 12 * t ^ 2 + 8 * t + 10 / 7) = (6 / 7 * t ^ 4 - 1 / 4 * t ^ 2 + 1 / 50) + (4 * t ^ 2 + t - 3 / 25) ^ 2 + (1221 / 100 * t ^ 2 + 206 / 25 * t + 493 / 350)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
