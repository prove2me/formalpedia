-- Prove2me | solution 1 for lean_workbook_plus_40666
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:03:31.21071+00:00
-- url     : https://prove2.me/submissions/ebfb49e1-3ec5-45c9-8c25-77ddcdda315f

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
theorem solution : ¬ (∀ (a : ℝ) (ha : 0 < a) (h : a^5 - a^3 + a = 2), 3 < a^3 ∧ a^3 < 4) := by
  have hex : ∃ a ∈ Set.Icc (1 : ℝ) (5/4), a^5-a^3+a=2 := intermediate_value_Icc (by norm_num) (by fun_prop) (by norm_num : (2 : ℝ) ∈ Set.Icc ((1 : ℝ)^5-1^3+1) ((5/4 : ℝ)^5-(5/4)^3+5/4))
  rcases hex with ⟨a, ha, he⟩
  have han : 0 ≤ a := by linarith only [ha.1]
  have hb : 0 ≤ (5/4-a)*(a^2+5/4*a+25/16) := mul_nonneg (by linarith only [ha.2]) (by positivity)
  intro h
  have hc := (h a (by linarith only [ha.1]) he).1
  clear h
  nlinarith only [hb, hc]
