-- Prove2me | solution 1 for lean_workbook_plus_66149
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:33.26023+00:00
-- url     : https://prove2.me/submissions/1f9e1d62-a689-4bbf-a658-a12ff9c9af3d

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n ≥ 3, 24 ≥ 6 ^ (n - 1)) := by
  push_neg
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
