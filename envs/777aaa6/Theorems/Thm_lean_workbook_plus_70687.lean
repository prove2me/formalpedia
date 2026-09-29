-- Prove2me | Theorems.Thm_lean_workbook_plus_70687
-- name    : lean_workbook_plus_70687
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a4a9b89e-faf9-4df9-a01a-181c06819cbc
-- statement:
--   Plugging this back in original system, we get\n $2a=b+c$ \n $2b=c+a$ \n $2c=a+b$ \nAnd so $a=b=c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70687 {a b c : ℝ} (h1 : a + b + c = 2 * a) (h2 : a + b + c = 2 * b) (h3 : a + b + c = 2 * c) : a = b ∧ b = c ∧ c = a   :=  by sorry
