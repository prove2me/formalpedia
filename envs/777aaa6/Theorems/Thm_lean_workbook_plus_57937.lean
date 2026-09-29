-- Prove2me | Theorems.Thm_lean_workbook_plus_57937
-- name    : lean_workbook_plus_57937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/76b85554-6a14-46c6-8a3a-f8c63aca4109
-- statement:
--   Show that if $a,b,c>0$ and $abc=1$ , then \n\n $\frac{1}{ab+a+1}+\frac{1}{bc+b+1}+\frac{1}{ca+c+1} =1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57937 (a b c : ℝ) (h1 : a>0 ∧ b>0 ∧ c>0 ∧ a * b * c = 1) : 1 / (a * b + a + 1) + 1 / (b * c + b + 1) + 1 / (c * a + c + 1) = 1   :=  by sorry
