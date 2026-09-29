-- Prove2me | solution 1 for lean_workbook_plus_75830
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:32.956844+00:00
-- url     : https://prove2.me/submissions/a8a566b3-4943-4faa-a5ea-cb1cc71cad39

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a+b+c)^2 ≥ a*b*c*(a+b+c) + 2 * (a^2 * b + b^2 * c + c^2 * a)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
