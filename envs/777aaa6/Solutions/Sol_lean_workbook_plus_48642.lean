-- Prove2me | solution 1 for lean_workbook_plus_48642
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:51.718012+00:00
-- url     : https://prove2.me/submissions/a0f8bde8-0bc3-4659-affc-bcc33a205d1a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y : ℝ, (x^2 + y^2 + 2) / (x^2 + 1) / (y^2 + 1) ≥ (10 * x * y + 7) / (x * y + 1) / (2 * x * y + 5)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
