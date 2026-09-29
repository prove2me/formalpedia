-- Prove2me | solution 1 for lean_workbook_plus_58450
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:26.579848+00:00
-- url     : https://prove2.me/submissions/900ef16b-1fb1-4206-9133-ec1d32d7002d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ n ≥ 6, 7*n - 12 ≥ 2^(n-1)) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(6), ?_⟩
  norm_num at *
