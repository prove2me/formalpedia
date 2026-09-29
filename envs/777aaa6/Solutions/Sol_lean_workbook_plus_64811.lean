-- Prove2me | solution 1 for lean_workbook_plus_64811
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T20:22:19.66536+00:00
-- url     : https://prove2.me/submissions/9cc51db7-7e15-4a30-82b9-af36614b5e4c

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
theorem solution : ¬ (∀ a b c d e : ℝ, (a / c + c / b + b / d + d / e + e / a) * (b / a + a / d + d / c + c / e + e / b) * (d / b + b / a + a / c + c / e + e / d) * (c / b + b / d + d / a + a / e + e / c) * (d / c + c / a + a / b + b / e + e / d) * (a / b + b / c + c / d + d / e + e / a) * (b / d + d / c + c / a + a / e + e / b) * (d / a + a / b + b / c + c / e + e / d) * (d / b + b / c + c / a + a / e + e / d) * (d / c + c / b + b / a + a / e + e / d) * (b / d + d / a + a / c + c / e + e / b) * (c / d + d / a + a / b + b / e + e / c) * (c / a + a / b + b / d + d / e + e / c) * (b / c + c / a + a / d + d / e + e / b) * (a / c + c / d + d / b + b / e + e / a) * (b / c + c / d + d / a + a / e + e / b) + (a / b + b / d + d / c + c / e + e / a) * (d / a + a / c + c / b + b / e + e / d) * (c / d + d / b + b / a + a / e + e / c) ≥ 281474976710656 * (a / (b + c + d + e) + b / (c + d + e + a) + c / (d + e + a + b) + d / (e + a + b + c) + e / (a + b + c + d))^24) := by
  push_neg
  try simp only [← funext_iff] at *
  norm_num at *
  refine ⟨(24), ?_⟩
  norm_num at *
  refine ⟨(24), ?_⟩
  norm_num at *
  refine ⟨(24), ?_⟩
  norm_num at *
  refine ⟨(24), ?_⟩
  norm_num at *
  refine ⟨(24), ?_⟩
  norm_num at *
  grind
