-- Prove2me | solution 1 for lean_workbook_plus_65582
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:36.591248+00:00
-- url     : https://prove2.me/submissions/bf2d6584-db1d-436e-ab42-e32727ef2aa3

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
theorem solution : ¬ (∀ (x : ℝ), -(-x^6 + Real.sqrt 3 * x^3 - 1) * (x^6 + Real.sqrt 3 * x^3 + 1) = 0) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(6), ?_⟩
  norm_num at *
  constructor
  · norm_num at *
    grind
  · norm_num at *
    grind
