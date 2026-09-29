-- Prove2me | solution 1 for lean_workbook_plus_78605
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:13.171166+00:00
-- url     : https://prove2.me/submissions/9a087c9e-2e81-435c-a779-4facf5cbc0a6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^2 / (2 * b + c) + b^2 / (2 * c + a) + c^2 / (2 * a + b) : ℝ) ≥ (a^2 + b^2 + c^2) / (a + b + c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
