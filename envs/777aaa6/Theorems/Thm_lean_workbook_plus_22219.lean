-- Prove2me | Theorems.Thm_lean_workbook_plus_22219
-- name    : lean_workbook_plus_22219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ae83d84f-0453-4863-b29c-44cc6a30969e
-- statement:
--   The equality holds when $ (a + b + c)^2 = 3(ab + bc + ca)\Longleftrightarrow (a - b)^2 + (b - c)^2 + (c - a)^2 = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22219 (a b c : ℝ) : (a + b + c) ^ 2 = 3 * (a * b + b * c + c * a) ↔ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0   :=  by sorry
