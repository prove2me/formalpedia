-- Prove2me | Theorems.Thm_lean_workbook_plus_75156
-- name    : lean_workbook_plus_75156
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b984967a-36cb-43d4-9e22-29e20a410f15
-- statement:
--   $\left(\frac{a.\frac{1}{b} +b.\frac{1}{c}+c.\frac{1}{a}+a.\frac{1}{a}}{4}\right)^2 \ge \left(\frac{(2a+b+c)(\frac{2}{a}+\frac{1}{b}+\frac{1}{c})}{16}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75156 : ∀ a b c : ℝ, (a * (1 / b) + b * (1 / c) + c * (1 / a) + a * (1 / a)) / 4 ≥ (2 * a + b + c) * (2 / a + 1 / b + 1 / c) / 16   :=  by sorry
