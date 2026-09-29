-- Prove2me | solution 1 for lean_workbook_plus_30828
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:02.19876+00:00
-- url     : https://prove2.me/submissions/79ed9779-a4e0-4df3-b1f3-59c5c4bd1e11

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
theorem solution : ¬ (∀ a b c : ℝ, a ∈ Set.Icc (1 / 2) 2 ∧ b ∈ Set.Icc (1 / 2) 2 ∧ c ∈ Set.Icc (1 / 2) 2 → 9 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) ∧ (a + b + c) * (1 / a + 1 / b + 1 / c) ≤ 10) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  intro
  norm_num at *
  grind
