-- Prove2me | Theorems.Thm_lean_workbook_plus_65601
-- name    : lean_workbook_plus_65601
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3741640b-bfa6-47be-b1e2-f994a2d71c60
-- statement:
--   Prove that $\frac{a^2+b^2+c^2}{(a+b+c)^2}+\frac{2ab}{(a+b)^2}+\frac{2bc}{(b+c)^2}+\frac{2ca}{(c+a)^2}\le \frac{11}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65601 : ∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a + b + c)^2 + 2 * a * b / (a + b)^2 + 2 * b * c / (b + c)^2 + 2 * c * a / (c + a)^2 ≤ 11 / 6   :=  by sorry
