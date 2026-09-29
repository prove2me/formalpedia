-- Prove2me | solution 1 for lean_workbook_plus_63747
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:40:35.844351+00:00
-- url     : https://prove2.me/submissions/26ca5e96-14d8-4596-acb3-bdbf6ade44ff

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c d e f : ℝ)
  (h₀ : a = 2 / 5 * 2013)
  (h₁ : b = 3 / 5 * 2013)
  (h₂ : c = 2 / 5 * 2013)
  (h₃ : d = 2 / 5 * 2013)
  (h₄ : e = 3 / 5 * 2013)
  (h₅ : f = 3 / 5 * 2013), a^2 + b^2 + c^2 + d^2 + e^2 + f^2 = 6 / 5 * 2013^2) := by
  push_neg
  norm_num at *
