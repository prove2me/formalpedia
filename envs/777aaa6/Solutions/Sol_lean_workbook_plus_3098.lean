-- Prove2me | solution 1 for lean_workbook_plus_3098
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:09.111136+00:00
-- url     : https://prove2.me/submissions/f3b37086-b49a-4eeb-8486-51ab94b62643

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x^2 + y^2 + z^2) / (2 * x^3 + 2 * y^3 + 2 * z^3 + 3) ≤ 1 / 3) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
