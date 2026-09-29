-- Prove2me | solution 1 for lean_workbook_plus_22947
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:09:35.06676+00:00
-- url     : https://prove2.me/submissions/30b818ca-5b9c-4036-9dc3-c5d3236f7b2a

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (h₁ : a = 0) (h₂ : c = 0), Set.univ = {x : ℝ | x^2 + b * x + 0 = 0}) := by
  intro h
  have he := h 0 0 0 rfl rfl
  have hm : (1 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 1
  rw [he] at hm
  norm_num at hm <;> grind only []
