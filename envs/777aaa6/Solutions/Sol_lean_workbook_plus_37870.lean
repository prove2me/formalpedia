-- Prove2me | solution 1 for lean_workbook_plus_37870
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:07.335717+00:00
-- url     : https://prove2.me/submissions/837322e7-d01a-4fb4-a6fa-4323dd37883b

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
theorem solution : ¬ (∀ a b c : ℝ, a * b * c ≤ 1 → a^2 * b^2 * c^2 + a * b * c + a * b * c * (a * b + b * c + c * a) + a * b * c * (a + b + c) ≤ a^2 + b^2 + c^2 + a + b + c + 2) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
  grind
