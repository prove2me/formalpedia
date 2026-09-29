-- Prove2me | solution 1 for lean_workbook_plus_20415
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:58.147371+00:00
-- url     : https://prove2.me/submissions/095bbeaa-8e5f-494a-bd30-706026fd8ecd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^2 * b^2 * c^2 + 8 * (a * b + b * c + a * c) ≤ 25) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
