-- Prove2me | solution 1 for lean_workbook_plus_25814
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:56.044757+00:00
-- url     : https://prove2.me/submissions/4abdc50e-035c-4820-83c9-4dbd0e7b679d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x z : ℝ, (3 + 4 * x - x ^ 2 - 8 * z) - x + 6 * z ≤ 5 + z ^ 2) := by
  push_neg
  refine ⟨1, -1, ?_⟩
  norm_num <;> grind
