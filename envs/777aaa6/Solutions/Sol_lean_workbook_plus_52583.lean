-- Prove2me | solution 1 for lean_workbook_plus_52583
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:11.874443+00:00
-- url     : https://prove2.me/submissions/695f6437-13e1-47b9-b8b0-3b9b6bea6714

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, (2:ℕ) ^ (n + 3) - (n + 3) + n + 2 = (2:ℕ) ^ (n + 3) - (n + 1)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
