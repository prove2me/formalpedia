-- Prove2me | solution 1 for lean_workbook_plus_15716
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:24.965502+00:00
-- url     : https://prove2.me/submissions/4d0e28b2-b7ee-4d3f-83ce-a0e7a257721e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (¬∃ f : ℕ → ℕ, ∀ n > 1, f n = f (f (n - 1)) + f (f (n + 1))) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
