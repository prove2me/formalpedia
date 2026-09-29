-- Prove2me | solution 1 for lean_workbook_plus_53634
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:47.712675+00:00
-- url     : https://prove2.me/submissions/1c52d8e2-b633-4342-9d50-e4b7b5892951

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (R r s : ℝ), 3 * R^2 - (s^4 - 8 * R * r * s^2 + 2 * r^2 * s^2 + 16 * R^2 * r^2 + 8 * R * r^3 + r^4) / (2 * (s^2 - 4 * R * r - r^2)) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
