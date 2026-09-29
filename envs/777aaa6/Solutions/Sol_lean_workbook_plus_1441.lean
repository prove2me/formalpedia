-- Prove2me | solution 1 for lean_workbook_plus_1441
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:48.743763+00:00
-- url     : https://prove2.me/submissions/fcb57a5a-cb30-4828-9714-44e1b384e7a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, (↑⌊a - 1 / 2⌋ + ↑⌊a + 1 / 2⌋) % 2 = 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
