-- Prove2me | solution 1 for lean_workbook_plus_26199
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:33.428229+00:00
-- url     : https://prove2.me/submissions/7ade7c69-6fee-4161-800e-41d175c4740b

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
theorem solution : ¬ (∀ t : ℝ, (Real.sqrt 2 - t) * (5 / Real.sqrt 2 - t) ≥ 0) := by
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hz : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  intro h
  have hc := h (2 * Real.sqrt 2)
  have he : (Real.sqrt 2 - 2 * Real.sqrt 2) * (5 / Real.sqrt 2 - 2 * Real.sqrt 2) = -1 := by
    field_simp
    nlinarith
  rw [he] at hc
  norm_num at hc
