-- Prove2me | solution 1 for lean_workbook_plus_36970
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:14:29.855828+00:00
-- url     : https://prove2.me/submissions/59605af7-6b13-433f-b460-0f724e5666f2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, 2 * (x * y + y * z + z * x) - (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
