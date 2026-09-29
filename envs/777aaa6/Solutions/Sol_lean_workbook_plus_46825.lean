-- Prove2me | solution 1 for lean_workbook_plus_46825
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:39:14.817473+00:00
-- url     : https://prove2.me/submissions/f81126db-4728-470e-abd5-0b51a6432f89

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x : ℝ)
  (h₀ : x^2 - 7 = x - 1), x^2 - x - 8 = 0) := by
  push_neg
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
