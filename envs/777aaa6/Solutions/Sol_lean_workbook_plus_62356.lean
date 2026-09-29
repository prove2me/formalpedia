-- Prove2me | solution 1 for lean_workbook_plus_62356
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:04.258001+00:00
-- url     : https://prove2.me/submissions/8ba32dcb-65c6-48f5-8484-584951654310

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a * b * c ≥ (4 * (a * b + b * c + c * a) * (a + b + c) - (a + b + c) ^ 3) / 9) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
