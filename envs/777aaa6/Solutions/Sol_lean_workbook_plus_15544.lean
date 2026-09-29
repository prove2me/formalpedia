-- Prove2me | solution 1 for lean_workbook_plus_15544
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:34:33.832122+00:00
-- url     : https://prove2.me/submissions/3d5f08ee-3685-4940-a096-e9c5a9982460

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p t : ℝ, (4 * p + 9) * (p - 3) ≥ (t - 3) * (36 - 8 * p)) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
