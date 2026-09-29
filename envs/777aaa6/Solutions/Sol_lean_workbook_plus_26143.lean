-- Prove2me | solution 1 for lean_workbook_plus_26143
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:42.601652+00:00
-- url     : https://prove2.me/submissions/e7c62596-8a05-4b5a-b2e1-69619903ad47

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (2 * a + b + 2 * c) + b / (2 * b + c + 2 * a) + c / (2 * c + a + 2 * b) : ℝ) ≤ 3 / 5) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
