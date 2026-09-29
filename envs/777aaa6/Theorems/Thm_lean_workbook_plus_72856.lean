-- Prove2me | Theorems.Thm_lean_workbook_plus_72856
-- name    : lean_workbook_plus_72856
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ebed9513-c931-4513-b2d3-04f7d31eb23a
-- statement:
--   The ineq is equivalent to $(ab+bc+ca)(a+b+c)+(ab+bc+ca)+6\ge 6(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72856 : ∀ a b c : ℝ, (a * b + b * c + c * a) * (a + b + c) + (a * b + b * c + c * a) + 6 ≥ 6 * (a + b + c)   :=  by sorry
