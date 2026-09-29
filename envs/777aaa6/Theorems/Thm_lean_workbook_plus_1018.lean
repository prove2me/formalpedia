-- Prove2me | Theorems.Thm_lean_workbook_plus_1018
-- name    : lean_workbook_plus_1018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cdfb9feb-6f40-417b-b18f-c1ae76ca58e9
-- statement:
--   Prove that $(ab+bc+ca)^2 \geq3abc(a+b+c).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1018 : ∀ a b c : ℝ, (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
