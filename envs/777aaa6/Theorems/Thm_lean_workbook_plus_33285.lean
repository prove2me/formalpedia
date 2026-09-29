-- Prove2me | Theorems.Thm_lean_workbook_plus_33285
-- name    : lean_workbook_plus_33285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c5d5fe34-4a7c-4f95-82c8-ee9338f382b2
-- statement:
--   Prove that $\frac{a}{b} + \frac{b}{a} = \frac{ a^2+b^2 }{ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33285  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0) :
  a / b + b / a = (a^2 + b^2) / (a * b)   :=  by sorry
