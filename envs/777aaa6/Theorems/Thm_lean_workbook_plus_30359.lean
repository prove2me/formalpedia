-- Prove2me | Theorems.Thm_lean_workbook_plus_30359
-- name    : lean_workbook_plus_30359
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8e5911ce-2411-4cdd-bafe-50270445091b
-- statement:
--   Solve for x\n$a = x; b = \sqrt{17-x^2}\na^2 + b^2 = 17\na+b+ab=9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30359 (a b : ℝ) (h₁ : a = x) (h₂ : b = Real.sqrt (17 - x^2)) (h₃ : a^2 + b^2 = 17) (h₄ : a + b + a * b = 9) : x = 2   :=  by sorry
