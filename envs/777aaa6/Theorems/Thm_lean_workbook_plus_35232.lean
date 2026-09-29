-- Prove2me | Theorems.Thm_lean_workbook_plus_35232
-- name    : lean_workbook_plus_35232
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0291be48-1ce4-4cbc-a9c2-d87b98cb13b1
-- statement:
--   Prove the inequality $\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{8abc}{(a+b)(b+c)(c+a)}\geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35232 : ∀ a b c : ℝ, (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 8 * a * b * c / (a + b) / (b + c) / (c + a) ≥ 2   :=  by sorry
