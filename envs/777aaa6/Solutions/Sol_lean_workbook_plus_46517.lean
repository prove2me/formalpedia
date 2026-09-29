-- Prove2me | solution 1 for lean_workbook_plus_46517
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:40.439437+00:00
-- url     : https://prove2.me/submissions/a38324e3-a842-4923-9957-bcb49dacabc6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (4 * (5 - x) ^ 2 / (31 - 11 * x) ≥ x / 5 + 3 ↔ 31 * x ^ 2 + 35 ≥ 66 * x)) := by
  push_neg
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
