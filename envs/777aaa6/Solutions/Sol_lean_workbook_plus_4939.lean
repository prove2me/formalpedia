-- Prove2me | solution 1 for lean_workbook_plus_4939
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:15.26597+00:00
-- url     : https://prove2.me/submissions/d64f9d63-0135-4852-98a4-35d13801c5f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ t1 t2 : ℝ, (1 + t1 ^ 2) * (1 + t2 ^ 2) ≥ (t1 * t2 + 1) ^ 2 ∧ (t1 * t2 + 1) ^ 2 ≥ (t1 + t2) * (t1 * t2 + 1)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
