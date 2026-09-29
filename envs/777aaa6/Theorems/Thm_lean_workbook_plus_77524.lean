-- Prove2me | Theorems.Thm_lean_workbook_plus_77524
-- name    : lean_workbook_plus_77524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/242d1283-2a64-4ce2-98dc-351e9f9e1fc5
-- statement:
--   By Difference of Cubes, $(10x^2)^3 - 1^3 = (10x^2-1)(100x^4+10x^2+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77524  (x : ℝ) :
  (10 * x^2)^3 - 1^3 = (10 * x^2 - 1) * (100 * x^4 + 10 * x^2 + 1)   :=  by sorry
