-- Prove2me | Theorems.Thm_lean_workbook_plus_14197
-- name    : lean_workbook_plus_14197
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3bec09f4-d608-45ba-b9ee-4f6af5f3d569
-- statement:
--   $\frac{a}{bc+1}+\frac{b}{ca+1}+\frac{c}{ab+1}+abc \le \frac{5}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14197 : ∀ a b c : ℝ, (a / (b * c + 1) + b / (c * a + 1) + c / (a * b + 1) + a * b * c ≤ 5 / 2)   :=  by sorry
