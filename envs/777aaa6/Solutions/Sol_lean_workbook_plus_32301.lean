-- Prove2me | solution 1 for lean_workbook_plus_32301
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:48.015011+00:00
-- url     : https://prove2.me/submissions/d8e31a37-178b-4453-ace2-689c6be432c1

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
theorem solution : ¬ (∀ x : ℝ, x < 1 / 12 → 1 / (1 + 6 * x ^ 2) ≥ -24 * x / 25 + 22 / 25) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(-24), ?_⟩
  norm_num at *
  grind
