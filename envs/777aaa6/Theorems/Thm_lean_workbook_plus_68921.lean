-- Prove2me | Theorems.Thm_lean_workbook_plus_68921
-- name    : lean_workbook_plus_68921
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a7e80500-c6ac-477a-9c86-3f38e30462a7
-- statement:
--   f(x) = $\sqrt {\frac{{{x^2} - 4x + 3}}{{{x^2} + x - 6}}} = \sqrt {\frac{{(x - 1)(x - 3)}}{{(x - 2)(x + 3)}}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68921  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ≠ 2)
  (h₂ : x ≠ -3)
  (h₃ : x^2 + x - 6 ≠ 0)
  (h₄ : x^2 - 4 * x + 3 ≥ 0) :
  Real.sqrt ((x^2 - 4 * x + 3) / (x^2 + x - 6)) = Real.sqrt ((x - 1) * (x - 3) / ((x - 2) * (x + 3)))   :=  by sorry
