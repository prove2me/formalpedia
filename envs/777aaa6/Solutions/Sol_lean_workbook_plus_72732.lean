-- Prove2me | solution 1 for lean_workbook_plus_72732
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:31:14.740602+00:00
-- url     : https://prove2.me/submissions/83fd053c-25d6-4736-9c9c-42ab08ee5c41

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (n : ℕ) (hn : 1 ≤ n), ∀ x y : ℕ, x^n+y^n ≤ 2^n+3^n) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
