-- Prove2me | solution 1 for lean_workbook_plus_53322
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:45:40.66802+00:00
-- url     : https://prove2.me/submissions/d9a03dcc-7773-4e91-b73d-10b9aaa32e42

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b + c - 1) ^ 2 - 1 ≥ (3 / 8 : ℝ) * (a + b) * (b + c) * (c + a)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
