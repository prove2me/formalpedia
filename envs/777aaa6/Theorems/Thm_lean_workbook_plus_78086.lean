-- Prove2me | Theorems.Thm_lean_workbook_plus_78086
-- name    : lean_workbook_plus_78086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ea9799d4-fe6d-4d86-9a07-5ddacf7008c7
-- statement:
--   Prove or disprove: If $x$ and $y$ are real numbers with $y\geq0$ and $y(y+1) \leq (x+1)^2$ , then $y(y-1)\leq x^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78086 (x y : ℝ) (hy : 0 ≤ y) (h : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2   :=  by sorry
