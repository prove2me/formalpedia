-- Prove2me | Theorems.Thm_lean_workbook_plus_23606
-- name    : lean_workbook_plus_23606
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8c734959-847e-445f-89fb-282ba88c8aba
-- statement:
--   After squaring of the both sides we obtain $(a-b)^2(x^2-ab)^2\geq0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23606 (a b x: ℝ) : (a - b) ^ 2 * (x ^ 2 - a * b) ^ 2 ≥ 0   :=  by sorry
