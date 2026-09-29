-- Prove2me | solution 1 for lean_workbook_plus_17212
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:47:06.193708+00:00
-- url     : https://prove2.me/submissions/ba410837-bce7-4901-b29d-82eed4b6e4a1

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
theorem solution : ¬ (∀ q, (3 - q) * (1 - (3 - q) / (Real.sqrt (q ^ 2 - 8 * q + 18) + Real.sqrt (9 - 2 * q))) ≥ 0) := by
  have hd : 0 < Real.sqrt 2+1 := by positivity
  have hn : (-1 : ℝ)/(Real.sqrt 2+1) < 0 := div_neg_of_neg_of_pos (by norm_num) hd
  have hb : 0 < 1-(-1 : ℝ)/(Real.sqrt 2+1) := by linarith only [hn]
  intro h
  have hc := h 4
  clear h
  rw [show (4 : ℝ)^2-8*4+18=2 by norm_num,show (9 : ℝ)-2*4=1 by norm_num,Real.sqrt_one,show (3 : ℝ)-4 = -1 by norm_num] at hc
  exact (not_le_of_gt (mul_neg_of_neg_of_pos (show (-1 : ℝ)<0 by norm_num) hb)) hc
