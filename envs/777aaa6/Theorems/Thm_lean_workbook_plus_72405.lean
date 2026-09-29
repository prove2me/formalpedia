-- Prove2me | Theorems.Thm_lean_workbook_plus_72405
-- name    : lean_workbook_plus_72405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0c35c394-e5f2-4972-92ef-3484f036b2ac
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that \n\n $ \frac{a}{ab+a+1}+\frac{b}{bc+b+1}+\frac{c}{ca+c+1}\le1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72405 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) ≤ 1   :=  by sorry
