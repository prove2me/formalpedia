-- Prove2me | solution 1 for lean_workbook_plus_41129
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:58.391172+00:00
-- url     : https://prove2.me/submissions/8efceb80-6306-4993-a6d5-515d9609ce72

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n : ℕ, 4 * n + 1 < (Real.sqrt n + Real.sqrt (n + 1))^2 ∧ (Real.sqrt n + Real.sqrt (n + 1))^2 < 4 * n + 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
