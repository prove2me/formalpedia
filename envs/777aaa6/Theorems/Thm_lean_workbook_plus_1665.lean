-- Prove2me | Theorems.Thm_lean_workbook_plus_1665
-- name    : lean_workbook_plus_1665
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/698c480e-d96d-4b8c-863a-e50bb6779dc3
-- statement:
--   Find the maximum value of $ac+bc-c^{2}-ab$ given $a-b=4$ where $a, b, c$ are real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1665 (a b c : ℝ) (h : a - b = 4) : a * c + b * c - c ^ 2 - a * b ≤ 4   :=  by sorry
