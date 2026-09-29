-- Prove2me | solution 1 for lean_workbook_plus_46631
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:06:20.711694+00:00
-- url     : https://prove2.me/submissions/39d262fe-11dd-4224-a6a1-ccbeb5f4a9cc

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
theorem solution : ¬ (∀ a b c : ℝ, 9^3 * (a^4 + 1)^3 * (b^4 + 1)^3 * (c^4 + 1)^3 ≥ 8^3 * (a^6 + a^3 + 1)^2 * (b^6 + b^3 + 1)^2 * (c^6 + c^3 + 1)^2 ∧ 8^3 * (a^6 + a^3 + 1)^2 * (b^6 + b^3 + 1)^2 * (c^6 + c^3 + 1)^2 >= 8^3 * (a^2 * b^2 * c^2 + a * b * c + 1)^6) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(8), ?_⟩
  norm_num at *
  refine ⟨(8), ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
