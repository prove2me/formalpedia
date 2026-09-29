-- Prove2me | solution 1 for lean_workbook_plus_29534
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:41.260991+00:00
-- url     : https://prove2.me/submissions/46702d7f-92f9-4e82-9c9f-ed570633a77e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a + b) / (a * b + 3) + (b + c) / (b * c + 3) + (c + a) / (c * a + 3) ≤ 3 / 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
