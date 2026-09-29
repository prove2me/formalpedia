-- Prove2me | solution 1 for lean_workbook_plus_72039
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:55.775518+00:00
-- url     : https://prove2.me/submissions/4e82bdd5-30bf-436e-bb6c-b3ea2ec48fa6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ A B C : ℝ, (A / (A + B) + B / (B + C) + C / (C + A)) < 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  3  ) , ?_⟩
  norm_num at *
