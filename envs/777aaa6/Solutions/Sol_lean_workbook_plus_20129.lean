-- Prove2me | solution 1 for lean_workbook_plus_20129
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:29.671093+00:00
-- url     : https://prove2.me/submissions/359b147a-497a-4889-ad96-9ff1113f5f40

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
theorem solution : ¬ (∀ n : ℕ, 2 ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 < a i ∧ a i < 1) → Real.sqrt (∏ i, a i) + Real.sqrt (∏ i, (1 - a i)) < 1) := by
  have hs : Real.sqrt ((1 / 2 : ℝ) * (1 / 2)) = 1 / 2 := Real.sqrt_mul_self (by norm_num)
  have hh : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  intro h
  have hc := h 2 (by norm_num) (fun _ => (1 / 2 : ℝ)) (by intro i; norm_num)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, hh, hs] at hc
  grind only []
