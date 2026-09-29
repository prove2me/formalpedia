-- Prove2me | Theorems.Thm_lean_workbook_plus_4188
-- name    : lean_workbook_plus_4188
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5352c1c1-f3db-416c-b6fd-b745fe80dd65
-- statement:
--   We have two numbers $a, b$ . We are given that $a+b = 50, ab = 25$ . Then $\frac{1}{a}+\frac{1}{b}= \frac{a+b}{ab}= \frac{50}{25}= \boxed{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4188 (a b : ℝ) (h₁ : a + b = 50) (h₂ : a * b = 25) : 1 / a + 1 / b = 2   :=  by sorry
