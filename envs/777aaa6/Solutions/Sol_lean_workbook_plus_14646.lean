-- Prove2me | solution 1 for lean_workbook_plus_14646
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:59.684386+00:00
-- url     : https://prove2.me/submissions/b727ade6-7f21-4f76-9735-7303defe5dc8

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
theorem solution : ¬ (∀ x > 0, Real.sqrt (x + 2 * Real.sqrt (x - 1)) + Real.sqrt (x - 2 * Real.sqrt (x - 1)) = 2 * Real.sqrt (x - 1)) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  grind
