-- Prove2me | solution 1 for lean_workbook_plus_75156
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:56.597283+00:00
-- url     : https://prove2.me/submissions/0b46b3b5-cc40-4ad7-9d07-2114bf32dbc7

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
theorem solution : ¬ (∀ a b c : ℝ, (a * (1 / b) + b * (1 / c) + c * (1 / a) + a * (1 / a)) / 4 ≥ (2 * a + b + c) * (2 / a + 1 / b + 1 / c) / 16) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(4), ?_⟩
  norm_num at *
  refine ⟨(4), ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  grind
