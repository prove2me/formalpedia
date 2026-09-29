-- Prove2me | solution 1 for lean_workbook_plus_19977
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:51.718202+00:00
-- url     : https://prove2.me/submissions/d1f12cbd-d012-4642-aebb-6520a7c379db

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 + a * b * c) / (a + b + c) ≤ (3 / 8) / (a + b + c) ∧ (3 / 8) / (a + b + c) ≤ 1 / 4) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
